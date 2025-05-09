package tastyquery.reader.classfiles

import scala.annotation.switch

import scala.collection.mutable

import tastyquery.Annotations.*
import tastyquery.Classpaths.*
import tastyquery.Contexts.*
import tastyquery.Constants.*
import tastyquery.Exceptions.*
import tastyquery.Flags
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.SourceLanguage
import tastyquery.SourcePosition
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

import tastyquery.reader.ReaderContext
import tastyquery.reader.ReaderContext.rctx
import tastyquery.reader.pickles.{Unpickler, PickleReader}

import ClassfileReader.{Annotation as CFAnnotation, *}
import ClassfileReader.Access.AccessFlags
import Constants.*

private[reader] object ClassfileParser {
  private val javaLangObjectBinaryName = termName("java/lang/Object")

  inline def innerClasses(using innerClasses: InnerClasses): innerClasses.type = innerClasses
  inline def resolver(using resolver: Resolver): resolver.type = resolver

  enum ClassKind:
    case Scala2, Java, TASTy, ScalaArtifact, JavaInnerOrArtifact

  case class InnerClassRef(innerSimpleName: SimpleName, outerBinaryName: SimpleName, isStatic: Boolean)

  case class InnerClassDecl(innerSimpleName: SimpleName, owner: DeclaringSymbol, innerBinaryName: SimpleName)

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

    def resolveStatic(binaryName: SimpleName)(using ReaderContext, InnerClasses): TermRef =
      lookup(binaryName, isStatic = true).asTermRef
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
      innerClasses: Forked[DataStream]
    ): InnerClasses =
      import structure.given

      val refsBuf = Map.newBuilder[SimpleName, InnerClassRef]
      val declsBuf = List.newBuilder[InnerClassDecl]
      innerClasses.use {
        ClassfileReader.readInnerClasses { (innerBinaryName, outerBinaryNameOpt, innerSimpleNameOpt, flags) =>
          // We don't care about local, anonymous or synthetic classes
          if outerBinaryNameOpt.isDefined && innerSimpleNameOpt.isDefined && !flags.is(Synthetic) then
            val outerBinaryName = outerBinaryNameOpt.get
            val innerSimpleName = innerSimpleNameOpt.get

            val isStatic = flags.is(Flags.Static)
            refsBuf += innerBinaryName -> InnerClassRef(innerSimpleName, outerBinaryName, isStatic)

            if outerBinaryName == structure.binaryName then
              val owner = if isStatic then moduleClass else cls
              declsBuf += InnerClassDecl(innerSimpleName, owner, innerBinaryName)
        }
      }
      InnerClasses(refsBuf.result(), declsBuf.result())
    end parse

    val Empty = InnerClasses(Map.empty, Nil)
  end InnerClasses

  def loadScala2Class(structure: Structure)(using ReaderContext): Unit = {
    import structure.given

    def failNoAnnot(): Nothing =
      throw Scala2PickleFormatException(
        s"class file for ${structure.binaryName} is a scala 2 class, " +
          "but it does not have the required annotation ScalaSignature or ScalaLongSignature"
      )

    val runtimeAnnotStart =
      structure.attributes
        .use(ClassfileReader.readAttribute(attr.RuntimeVisibleAnnotations))
        .getOrElse(failNoAnnot())

    val scalaSigAnnotation =
      runtimeAnnotStart
        .use(ClassfileReader.readAnnotation(Set(annot.ScalaLongSignature, annot.ScalaSignature)))
        .getOrElse(failNoAnnot())

    val sigBytes = (scalaSigAnnotation.tpe: @unchecked) match {
      case annot.ScalaSignature =>
        val bytesArg = scalaSigAnnotation.values.head._2.asInstanceOf[AnnotationValue.Const]
        pool.sigbytes(bytesArg.valueIdx)
      case annot.ScalaLongSignature =>
        val bytesArrArg = scalaSigAnnotation.values.head._2.asInstanceOf[AnnotationValue.Arr]
        val idxs = bytesArrArg.values.map(_.asInstanceOf[AnnotationValue.Const].valueIdx)
        pool.sigbytes(idxs)
    }
    Unpickler.loadInfo(sigBytes)
  }

  def loadJavaClass(classOwner: DeclaringSymbol, name: SimpleName, structure: Structure)(
    using ReaderContext,
    Resolver
  ): List[InnerClassDecl] = {
    import structure.given

    val attributes = structure.attributes.use(ClassfileReader.readAttributeMap())

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
      .setTypeParams(Nil)
      .setFlags(clsFlags | Flags.ModuleClassCreationFlags, clsPrivateWithin)
      .setAnnotations(Nil)
      .setParentsDirect(rctx.ObjectType :: Nil)
      .setGivenSelfType(None)
    allRegisteredSymbols += moduleClass

    val module = TermSymbol
      .create(name, classOwner)
      .setDeclaredType(moduleClass.localRef)
      .setFlags(clsFlags | Flags.ModuleValCreationFlags, clsPrivateWithin)
      .setAnnotations(Nil)
    allRegisteredSymbols += module

    val innerClassesStrict: InnerClasses =
      attributes.get(attr.InnerClasses) match
        case None         => InnerClasses.Empty
        case Some(stream) => InnerClasses.parse(cls, moduleClass, structure, stream)
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

    def createMember(
      name: SimpleName,
      isMethod: Boolean,
      javaFlags: AccessFlags,
      descriptor: String,
      attributes: Map[SimpleName, Forked[DataStream]]
    ): TermSymbol =
      // Select the right owner and create the symbol
      val owner = if javaFlags.isStatic then moduleClass else cls
      val sym = TermSymbol.create(name, owner)
      allRegisteredSymbols += sym

      // Read parameter names
      val methodParamNames =
        if isMethod then readMethodParameters(attributes).map(_._1)
        else Nil

      // Find the signature, or fall back to the descriptor
      val memberSig = attributes.get(attr.Signature) match
        case Some(stream) => stream.use(ClassfileReader.readSignature)
        case None         => descriptor

      // Parse the signature into a declared type for the symbol
      val declaredType =
        val parsedType = JavaSignatures.parseSignature(sym, isMethod, methodParamNames, memberSig, allRegisteredSymbols)
        val adaptedType =
          if isMethod && sym.name == nme.Constructor then cls.makePolyConstructorType(parsedType)
          else if isMethod && javaFlags.isVarargsIfMethod then patchForVarargs(sym, parsedType)
          else parsedType
        adaptedType
      end declaredType
      sym.setDeclaredType(declaredType)

      // Compute the flags for the symbol
      val flags =
        var flags1 = javaFlags.toFlags | JavaDefined
        if isMethod then flags1 |= Method
        if isSignaturePolymorphic(isMethod, javaFlags, declaredType) then flags1 |= SignaturePolymorphic
        flags1
      end flags
      sym.setFlags(flags, privateWithin(javaFlags))

      // Read and fill annotations
      val annots = readAnnotations(sym, attributes)
      sym.setAnnotations(annots)

      // Handle parameters
      if isMethod then
        // Auto fill the param symbols from the declared type
        sym.autoFillParamSymss()

        val termParamAnnots = readTermParamAnnotations(attributes)
        if termParamAnnots.isEmpty then
          // fast path
          sym.paramSymss.foreach(_.merge.foreach(_.setAnnotations(Nil)))
        else
          val termParamAnnotsIter = termParamAnnots.iterator

          for paramSyms <- sym.paramSymss do
            paramSyms match
              case Left(termParamSyms) =>
                for termParamSym <- termParamSyms do
                  val annots = if termParamAnnotsIter.hasNext then termParamAnnotsIter.next() else Nil
                  termParamSym.setAnnotations(annots)
              case Right(typeParamSyms) =>
                // TODO Maybe one day we also read type annotations
                typeParamSyms.foreach(_.setAnnotations(Nil))
        end if
      end if

      sym
    end createMember

    def loadMembers(): Unit =
      structure.fields.use {
        ClassfileReader.readMembers { (javaFlags, name, descriptor, attributes) =>
          createMember(name, isMethod = false, javaFlags, descriptor, attributes)
        }
      }
      structure.methods.use {
        ClassfileReader.readMembers { (javaFlags, name, descriptor, attributes) =>
          createMember(name, isMethod = true, javaFlags, descriptor, attributes)
        }
      }
    end loadMembers

    def initParents(): Unit =
      def binaryName(cls: ConstantInfo.Class) =
        pool.utf8(cls.nameIdx)

      val parents = attributes.get(attr.Signature) match
        case Some(stream) =>
          val sig = stream.use(ClassfileReader.readSignature)
          val parsedSig =
            JavaSignatures.parseSignature(cls, isMethod = false, methodParameterNames = Nil, sig, allRegisteredSymbols)
          parsedSig.requireType match
            case mix: AndType => mix.parts
            case sup          => sup :: Nil
        case None =>
          structure.supers.use {
            val superClass = ClassfileReader.readSuperClass().map(binaryName)
            val interfaces = ClassfileReader.readInterfaces().map(binaryName)
            JavaSignatures.parseSupers(cls, superClass, interfaces)
          }
      end parents

      val parents1 =
        if parents.head eq rctx.FromJavaObjectType then rctx.ObjectType :: parents.tail
        else parents
      cls.setParentsDirect(parents1)
    end initParents

    cls.setGivenSelfType(None)
    cls.setFlags(clsFlags, clsPrivateWithin)
    initParents()

    // Intercept special classes to create their magic methods
    if cls.isAnySpecialClass then
      if cls.isObject then rctx.createObjectMagicMethods(cls)
      else if cls.isString then rctx.createStringMagicMethods(cls)
      else if cls.isJavaEnum then rctx.createEnumMagicMethods(cls)

    // Synthesize a constructor for interfaces
    if cls.isTrait then
      val ctor = TermSymbol
        .create(nme.Constructor, cls)
        .setDeclaredType(cls.makePolyConstructorType(MethodType(Nil, Nil, rctx.UnitType)))
        .setFlags(Method | JavaDefined, None)
        .setAnnotations(Nil)
        .autoFillParamSymss()
      ctor.paramSymss.foreach(_.merge.foreach(_.setAnnotations(Nil)))
      allRegisteredSymbols += ctor
    end if

    loadMembers()

    val annotations = readAnnotations(cls, attributes)
    cls.setAnnotations(annotations)

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

  private def readMethodParameters(attributes: AttributeMap)(
    using ConstantPool
  ): List[(UnsignedTermName, AccessFlags)] =
    attributes.get(attr.MethodParameters) match
      case Some(stream) => stream.use(ClassfileReader.readMethodParameters())
      case None         => Nil
  end readMethodParameters

  private def readAnnotations(
    sym: TermOrTypeSymbol,
    attributes: AttributeMap
  )(using ConstantPool, ReaderContext, InnerClasses, Resolver): List[Annotation] =
    readAnnotations(sym, attributes.get(attr.RuntimeVisibleAnnotations))
      ::: readAnnotations(sym, attributes.get(attr.RuntimeInvisibleAnnotations))
  end readAnnotations

  private def readAnnotations(
    sym: TermOrTypeSymbol,
    annotationsStream: Option[Forked[DataStream]]
  )(using ConstantPool, ReaderContext, InnerClasses, Resolver): List[Annotation] =
    annotationsStream.fold(Nil)(readAnnotations(sym, _))
  end readAnnotations

  private def readAnnotations(
    sym: TermOrTypeSymbol,
    annotationsStream: Forked[DataStream]
  )(using ConstantPool, ReaderContext, InnerClasses, Resolver): List[Annotation] =
    val classfileAnnots = annotationsStream.use(ClassfileReader.readAllAnnotations())
    classfileAnnots.map(classfileAnnotToAnnot(_))

  private def readTermParamAnnotations(
    attributes: AttributeMap
  )(using ConstantPool, ReaderContext, InnerClasses, Resolver): List[List[Annotation]] =
    val runtimeVisible = attributes.get(attr.RuntimeVisibleParameterAnnotations) match
      case None         => Nil
      case Some(stream) => stream.use(ClassfileReader.readAllParameterAnnotations())

    val runtimeInvisible = attributes.get(attr.RuntimeInvisibleParameterAnnotations) match
      case None         => Nil
      case Some(stream) => stream.use(ClassfileReader.readAllParameterAnnotations())

    if runtimeVisible.isEmpty && runtimeInvisible.isEmpty then
      // fast path
      Nil
    else
      for (rtVisible, rtInvisible) <- runtimeVisible.zipAll(runtimeInvisible, Nil, Nil)
      yield (rtVisible ::: rtInvisible).map(classfileAnnotToAnnot(_))
  end readTermParamAnnotations

  private def classfileAnnotToAnnot(
    classfileAnnot: CFAnnotation
  )(using ConstantPool, ReaderContext, InnerClasses, Resolver): Annotation =
    val annotationType = JavaSignatures.parseFieldDescriptor(classfileAnnot.tpe.name)

    val args: List[TermTree] =
      for (name, value) <- classfileAnnot.values.toList yield
        val valueTree = annotationValueToTree(value)
        NamedArg(name, valueTree)(SourcePosition.NoPosition)

    Annotation.fromAnnotTypeAndArgs(annotationType, args)
  end classfileAnnotToAnnot

  private def annotationValueToTree(
    value: AnnotationValue
  )(using ConstantPool, ReaderContext, InnerClasses, Resolver): TermTree =
    import AnnotationValue.Tags

    val pool = summon[ConstantPool]
    val pos = SourcePosition.NoPosition

    value match
      case AnnotationValue.Const(tag, valueIdx) =>
        val constant = (tag: @switch) match
          case Tags.Byte    => Constant(pool.integer(valueIdx).toByte)
          case Tags.Char    => Constant(pool.integer(valueIdx).toChar)
          case Tags.Double  => Constant(pool.double(valueIdx))
          case Tags.Float   => Constant(pool.float(valueIdx))
          case Tags.Int     => Constant(pool.integer(valueIdx))
          case Tags.Long    => Constant(pool.long(valueIdx))
          case Tags.Short   => Constant(pool.integer(valueIdx).toShort)
          case Tags.Boolean => Constant(pool.integer(valueIdx) != 0)
          case Tags.String  => Constant(pool.utf8(valueIdx).name)
        Literal(constant)(pos)

      case AnnotationValue.EnumConst(descriptor, constName) =>
        /* JVMS says that it can be any field descriptor,
         * but I don't see what we would do with a base type or array type.
         */
        val binaryName = descriptor.name match
          case s"L$binaryName;" => binaryName
          case other            => throw ClassfileFormatException(s"unexpected non-class field descriptor: $other")
        val enumClassStaticRef = resolver.resolveStatic(termName(binaryName))
        val constRef = TermRef(enumClassStaticRef, constName)
        Ident(constName)(constRef)(pos)

      case AnnotationValue.ClassConst(descriptor) =>
        val classType = JavaSignatures.parseReturnDescriptor(descriptor.name)
        Literal(Constant(classType))(pos)

      case AnnotationValue.NestedAnnotation(annotation) =>
        val nestedAnnot = classfileAnnotToAnnot(annotation)
        nestedAnnot.tree

      case AnnotationValue.Arr(values) =>
        val valueTrees = values.map(annotationValueToTree(_)).toList
        val elemType = rctx.AnyType // TODO This will not be type-correct
        SeqLiteral(valueTrees, TypeWrapper(elemType)(pos))(pos)
  end annotationValueToTree

  def detectClassKind(structure: Structure): ClassKind =
    import structure.given

    var innerClassesStream: Forked[DataStream] | Null = null

    var result: ClassKind = ClassKind.Java // if we do not find anything special, it will be Java
    structure.attributes.use {
      ClassfileReader.scanAttributes {
        case attr.ScalaSig =>
          result = ClassKind.Scala2
          true
        case attr.Scala =>
          result = ClassKind.ScalaArtifact
          false // keep going; there might be a ScalaSig or TASTY later on
        case attr.TASTY =>
          result = ClassKind.TASTy
          true
        case attr.InnerClasses =>
          innerClassesStream = data.fork
          false
        case _ =>
          false
      }
    }

    if result == ClassKind.Java && innerClassesStream != null then
      if containsSelfInnerClassDecl(structure.binaryName, innerClassesStream.nn) then ClassKind.JavaInnerOrArtifact
      else ClassKind.Java
    else result
  end detectClassKind

  private def containsSelfInnerClassDecl(binaryName: SimpleName, innerClassesStream: Forked[DataStream])(
    using ConstantPool
  ): Boolean =
    innerClassesStream.use {
      var result = false
      ClassfileReader.readInnerClasses { (innerFullBinaryName, _, _, _) =>
        result ||= (innerFullBinaryName == binaryName)
      }
      result
    }
  end containsSelfInnerClassDecl
}
