package tastyquery.reader.classfiles

import scala.collection.mutable

import tastyquery.Annotations.Annotation as TQAnnotation
import tastyquery.Classpaths.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.SourceLanguage
import tastyquery.Symbols.*
import tastyquery.Types.*

import tastyquery.reader.ReaderContext
import tastyquery.reader.ReaderContext.rctx
import tastyquery.reader.pickles.{Unpickler, PickleReader}

import ClassfileReader.*
import ClassfileReader.Access.AccessFlags
import Constants.*

private[reader] object ClassfileParser {
  private val javaLangObjectBinaryName = termName("java/lang/Object")

  inline def innerClasses(using innerClasses: InnerClasses): innerClasses.type = innerClasses
  inline def resolver(using resolver: Resolver): resolver.type = resolver

  enum ClassKind:
    case Scala2(structure: Structure, runtimeAnnotStart: Forked[DataStream])
    case Java(structure: Structure, classSig: SigOrSupers, inners: Option[Forked[DataStream]])
    case TASTy
    case Artifact

  case class InnerClassRef(name: SimpleName, outer: SimpleName, isStatic: Boolean)

  case class InnerClassDecl(classData: ClassData, name: SimpleName, owner: DeclaringSymbol)

  class Resolver:
    private val refs = mutable.HashMap.empty[SimpleName, TypeRef]
    private val staticrefs = mutable.HashMap.empty[SimpleName, TermRef]

    private def computeRef(binaryName: SimpleName, isStatic: Boolean)(using ReaderContext, InnerClasses): NamedType =
      innerClasses.get(binaryName) match
        case Some(InnerClassRef(name, outer, isStaticInner)) =>
          val pre = lookup(outer, isStaticInner)
          NamedType(pre, if isStatic then name else name.toTypeName)
        case None if !isStatic && binaryName == javaLangObjectBinaryName =>
          rctx.FromJavaObjectType
        case None =>
          val (pkgRef, cls) = binaryName.name.lastIndexOf('/') match
            case -1 => (rctx.RootPackage.packageRef, binaryName)
            case i  => (computePkg(binaryName.name.take(i)), termName(binaryName.name.drop(i + 1)))
          NamedType(pkgRef, if isStatic then cls else cls.toTypeName)
    end computeRef

    private def computePkg(packageName: String)(using ReaderContext): TermReferenceType =
      val parts = packageName.split('/').map(termName).toList
      rctx.createPackageSelection(parts)

    private def lookup(binaryName: SimpleName, isStatic: Boolean)(using ReaderContext, InnerClasses): NamedType =
      if isStatic then staticrefs.getOrElseUpdate(binaryName, computeRef(binaryName, isStatic = true).asTermRef)
      else refs.getOrElseUpdate(binaryName, computeRef(binaryName, isStatic = false).asTypeRef)

    def resolve(binaryName: SimpleName)(using ReaderContext, InnerClasses): TypeRef =
      lookup(binaryName, isStatic = false).asTypeRef

  end Resolver

  /** The inner classes local to a class file */
  class InnerClasses private (refs: Map[SimpleName, InnerClassRef], decls: List[InnerClassDecl]):
    def get(binaryName: SimpleName): Option[InnerClassRef] =
      refs.get(binaryName)

    /** The inner class declarations of the associated classfile */
    def declarations: List[InnerClassDecl] =
      decls

  object InnerClasses:
    def parse(
      cls: ClassSymbol,
      moduleClass: ClassSymbol,
      structure: Structure,
      lookup: Map[SimpleName, ClassData],
      innerClasses: Forked[DataStream]
    ): InnerClasses =
      import structure.given

      def missingClass(binaryName: SimpleName) =
        ClassfileFormatException(s"Inner class $binaryName not found, keys: ${lookup.keys.toList}")

      def lookupDeclaration(isStatic: Boolean, name: SimpleName, binaryName: SimpleName): InnerClassDecl =
        val data = lookup.getOrElse(binaryName, throw missingClass(binaryName))
        InnerClassDecl(data, name, if isStatic then moduleClass else cls)

      val refsBuf = Map.newBuilder[SimpleName, InnerClassRef]
      val declsBuf = List.newBuilder[InnerClassDecl]
      innerClasses.use {
        ClassfileReader.readInnerClasses { (name, innerBinaryName, outerBinaryName, flags) =>
          val isStatic = flags.is(Flags.Static)
          refsBuf += innerBinaryName -> InnerClassRef(name, outerBinaryName, isStatic)
          if outerBinaryName == structure.binaryName then declsBuf += lookupDeclaration(isStatic, name, innerBinaryName)
        }
      }
      InnerClasses(refsBuf.result(), declsBuf.result())
    end parse

    val Empty = InnerClasses(Map.empty, Nil)
  end InnerClasses

  class Structure(
    val access: AccessFlags,
    val binaryName: SimpleName,
    val supers: Forked[DataStream],
    val fields: Forked[DataStream],
    val methods: Forked[DataStream],
    val attributes: Forked[DataStream]
  )(using val pool: ConstantPool)

  def loadScala2Class(structure: Structure, runtimeAnnotStart: Forked[DataStream])(using ReaderContext): Unit = {
    import structure.given

    val Some(Annotation(tpe, args)) = runtimeAnnotStart.use {
      ClassfileReader.readAnnotation(Set(annot.ScalaLongSignature, annot.ScalaSignature))
    }: @unchecked

    val sigBytes = tpe match {
      case annot.ScalaSignature =>
        val bytesArg = args.head.asInstanceOf[AnnotationValue.Const]
        pool.sigbytes(bytesArg.valueIdx)
      case annot.ScalaLongSignature =>
        val bytesArrArg = args.head.asInstanceOf[AnnotationValue.Arr]
        val idxs = bytesArrArg.values.map(_.asInstanceOf[AnnotationValue.Const].valueIdx)
        pool.sigbytes(idxs)
    }
    Unpickler.loadInfo(sigBytes)

  }

  def loadJavaClass(
    classOwner: DeclaringSymbol,
    name: SimpleName,
    structure: Structure,
    classSig: SigOrSupers,
    innerLookup: Map[SimpleName, ClassData],
    optInnerClasses: Option[Forked[DataStream]]
  )(using ReaderContext, Resolver): List[InnerClassDecl] = {
    import structure.given

    val allRegisteredSymbols = mutable.ListBuffer.empty[TermOrTypeSymbol]

    val cls = ClassSymbol.create(name.toTypeName, classOwner)
    allRegisteredSymbols += cls

    def privateWithin(access: AccessFlags): Option[PackageSymbol] =
      def enclosingPackage(sym: Symbol): PackageSymbol = sym match
        case sym: PackageSymbol    => sym
        case sym: TermOrTypeSymbol => enclosingPackage(sym.owner)
      if access.isPackagePrivate then Some(enclosingPackage(classOwner)) else None

    val clsFlags = structure.access.toFlags | JavaDefined
    val clsPrivateWithin = privateWithin(structure.access)

    val moduleClass = ClassSymbol
      .create(name.withObjectSuffix.toTypeName, classOwner)
      .withTypeParams(Nil)
      .withFlags(clsFlags | Flags.ModuleClassCreationFlags, clsPrivateWithin)
      .setAnnotations(Nil)
      .withParentsDirect(rctx.ObjectType :: Nil)
      .withGivenSelfType(None)
    allRegisteredSymbols += moduleClass

    val module = TermSymbol
      .create(name, classOwner)
      .withDeclaredType(moduleClass.localRef)
      .withFlags(clsFlags | Flags.ModuleValCreationFlags, clsPrivateWithin)
      .setAnnotations(Nil)
    allRegisteredSymbols += module

    def readInnerClasses(innerClasses: Forked[DataStream]): InnerClasses =
      InnerClasses.parse(cls, moduleClass, structure, innerLookup, innerClasses)

    val innerClassesStrict = optInnerClasses.map(readInnerClasses).getOrElse(InnerClasses.Empty)
    given InnerClasses = innerClassesStrict

    /* Does this class contain signature-polymorphic methods?
     *
     * See https://scala-lang.org/files/archive/spec/3.4/06-expressions.html#signature-polymorphic-methods
     */
    val clsContainsSigPoly: Boolean =
      classOwner == rctx.javaLangInvokePackage
        && (cls.name == tpnme.MethodHandle || cls.name == tpnme.VarHandle)

    /* Is the member with the given properties signature-polymorphic? */
    def isSignaturePolymorphic(isMethod: Boolean, javaFlags: AccessFlags, declaredType: TypeOrMethodic): Boolean =
      if clsContainsSigPoly && isMethod && javaFlags.isNativeVarargsIfMethod then
        declaredType match
          case mt: MethodType if mt.paramNames.sizeIs == 1 => true
          case _                                           => false
      else false
    end isSignaturePolymorphic

    def createMember(name: SimpleName, isMethod: Boolean, javaFlags: AccessFlags, memberSig: MemberSig): TermSymbol =
      // Select the right owner and create the symbol
      val owner = if javaFlags.isStatic then moduleClass else cls
      val sym = TermSymbol.create(name, owner)
      allRegisteredSymbols += sym

      // Parse the signature into a declared type for the symbol
      val declaredType =
        val parsedType = JavaSignatures.parseSignature(sym, isMethod, memberSig, allRegisteredSymbols)
        val adaptedType =
          if isMethod && sym.name == nme.Constructor then cls.makePolyConstructorType(parsedType)
          else if isMethod && javaFlags.isVarargsIfMethod then patchForVarargs(sym, parsedType)
          else parsedType
        adaptedType
      end declaredType
      sym.withDeclaredType(declaredType)

      // Compute the flags for the symbol
      val flags =
        var flags1 = javaFlags.toFlags | JavaDefined
        if isMethod then flags1 |= Method
        if isSignaturePolymorphic(isMethod, javaFlags, declaredType) then flags1 |= SignaturePolymorphic
        flags1
      end flags
      sym.withFlags(flags, privateWithin(javaFlags))

      // Auto fill the param symbols from the declared type
      sym.autoFillParamSymss()

      sym.setAnnotations(Nil) // TODO Read Java annotations on fields and methods

      sym
    end createMember

    def loadMembers(): Unit =
      structure.fields.use {
        ClassfileReader.readFields { (name, sigOrDesc, javaFlags) =>
          createMember(name, isMethod = false, javaFlags, sigOrDesc)
        }
      }
      structure.methods.use {
        ClassfileReader.readMethods { (name, sigOrDesc, javaFlags) =>
          createMember(name, isMethod = true, javaFlags, sigOrDesc)
        }
      }
    end loadMembers

    def initParents(): Unit =
      def binaryName(cls: ConstantInfo.Class) =
        pool.utf8(cls.nameIdx)
      val parents = classSig match
        case SigOrSupers.Sig(sig) =>
          JavaSignatures.parseSignature(cls, isMethod = false, sig, allRegisteredSymbols).requireType match
            case mix: AndType => mix.parts
            case sup          => sup :: Nil
        case SigOrSupers.Supers =>
          structure.supers.use {
            val superClass = ClassfileReader.readSuperClass().map(binaryName)
            val interfaces = ClassfileReader.readInterfaces().map(binaryName)
            JavaSignatures.parseSupers(cls, superClass, interfaces)
          }
      end parents
      val parents1 =
        if parents.head eq rctx.FromJavaObjectType then rctx.ObjectType :: parents.tail
        else parents
      cls.withParentsDirect(parents1)
    end initParents

    cls.withGivenSelfType(None)
    cls.withFlags(clsFlags, clsPrivateWithin)
    cls.setAnnotations(Nil) // TODO Read Java annotations on classes
    initParents()

    // Intercept special classes to create their magic methods
    if cls.isAnySpecialClass then
      if cls.isObject then rctx.createObjectMagicMethods(cls)
      else if cls.isString then rctx.createStringMagicMethods(cls)
      else if cls.isJavaEnum then rctx.createEnumMagicMethods(cls)

    loadMembers()

    for sym <- allRegisteredSymbols do
      sym.checkCompleted()
      assert(sym.sourceLanguage == SourceLanguage.Java, s"$sym of ${sym.getClass()}")

    innerClasses.declarations
  }

  private def patchForVarargs(sym: TermSymbol, tpe: TypeOrMethodic)(using ReaderContext): MethodicType =
    tpe match
      case tpe: MethodType if tpe.paramNames.sizeIs >= 1 =>
        val patchedLast = tpe.paramTypes.last match
          case ArrayTypeExtractor(lastElemType) =>
            RepeatedType(lastElemType.requireType)
          case _ =>
            throw ClassfileFormatException(s"Found ACC_VARARGS on $sym but its last param type was not an array: $tpe")
        tpe.derivedLambdaType(tpe.paramNames, tpe.paramTypes.init :+ patchedLast, tpe.resultType)
      case tpe: PolyType =>
        tpe.derivedLambdaType(tpe.paramNames, tpe.paramTypeBounds, patchForVarargs(sym, tpe.resultType))
      case _ =>
        throw ClassfileFormatException(s"Found ACC_VARARGS on $sym but its type was not a MethodType: $tpe")
  end patchForVarargs

  /** Extracts `elemType` from `AppliedType(scala.Array, List(elemType))`.
    *
    * This works for array types created by `defn.ArrayTypeOf(elemType)`, but
    * is not otherwise guaranteed to work in all situations.
    */
  private object ArrayTypeExtractor:
    def unapply(tpe: AppliedType)(using ReaderContext): Option[TypeOrWildcard] =
      tpe.tycon match
        case tycon: TypeRef if tycon.name == tpnme.Array && tpe.args.sizeIs == 1 =>
          tycon.prefix match
            case prefix: PackageRef if prefix.symbol.isScalaPackage =>
              Some(tpe.args.head)
            case _ =>
              None
        case _ =>
          None
  end ArrayTypeExtractor

  private def parse(classRoot: ClassData, structure: Structure): ClassKind = {
    import structure.given

    var runtimeAnnotStart: Forked[DataStream] | Null = null
    var innerClassesStart: Option[Forked[DataStream]] = None
    var sigOrNull: String | Null = null
    var isScala = false
    var isTASTY = false
    var isScalaRaw = false
    structure.attributes.use {
      ClassfileReader.scanAttributes {
        case attr.ScalaSig =>
          isScala = true
          runtimeAnnotStart != null
        case attr.Scala =>
          isScalaRaw = true
          true
        case attr.TASTY =>
          isTASTY = true
          true
        case attr.RuntimeVisibleAnnotations =>
          runtimeAnnotStart = data.fork
          isScala
        case attr.Signature =>
          if !(isScala || isScalaRaw || isTASTY) then sigOrNull = data.fork.use(ClassfileReader.readSignature)
          false
        case attr.InnerClasses =>
          if !(isScala || isScalaRaw || isTASTY) then innerClassesStart = Some(data.fork)
          false
        case _ =>
          false
      }
      isScalaRaw &= !isTASTY
    }
    if isScala then
      val annots = runtimeAnnotStart
      if annots != null then ClassKind.Scala2(structure, annots)
      else
        throw Scala2PickleFormatException(
          s"class file for ${classRoot.binaryName} is a scala 2 class, but has no annotations"
        )
    else if isTASTY then ClassKind.TASTy
    else if isScalaRaw then ClassKind.Artifact
    else
      val sig = sigOrNull
      val classSig = if sig != null then SigOrSupers.Sig(sig) else SigOrSupers.Supers
      ClassKind.Java(structure, classSig, innerClassesStart)
  }

  private def readStructure()(using pool: ConstantPool)(using DataStream): Structure = {
    val access = ClassfileReader.readAccessFlags()
    val thisClass = ClassfileReader.readThisClass()
    val supers = data.forkAndSkip {
      data.skip(2) // superclass
      data.skip(2 * data.readU2()) // interfaces
    }
    Structure(
      access = access,
      binaryName = pool.utf8(thisClass.nameIdx),
      supers = supers,
      fields = ClassfileReader.skipFields(),
      methods = ClassfileReader.skipMethods(),
      attributes = ClassfileReader.skipAttributes()
    )
  }

  private def toplevel(classOwner: DeclaringSymbol, classRoot: ClassData): Structure =
    ClassfileReader.unpickle(classRoot) {
      ClassfileReader.acceptHeader(classOwner, classRoot)
      val pool = ClassfileReader.readConstantPool()
      readStructure()(using pool)
    }
  end toplevel

  def readKind(classOwner: DeclaringSymbol, classRoot: ClassData): ClassKind =
    parse(classRoot, toplevel(classOwner, classRoot))

}
