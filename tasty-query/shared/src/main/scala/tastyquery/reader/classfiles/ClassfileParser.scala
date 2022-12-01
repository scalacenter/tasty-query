package tastyquery.reader.classfiles

import scala.collection.mutable

import tastyquery.Classpaths.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Types.*

import tastyquery.reader.pickles.{Unpickler, PickleReader}

import ClassfileReader.*
import ClassfileReader.Access.AccessFlags

private[reader] object ClassfileParser {

  transparent inline def innerClasses(using innerClasses: InnerClasses): innerClasses.type = innerClasses
  transparent inline def resolver(using resolver: Resolver): resolver.type = resolver

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

    private def computeRef(binaryName: SimpleName, isStatic: Boolean)(using Context, InnerClasses): NamedType =
      innerClasses.get(binaryName) match
        case Some(InnerClassRef(name, outer, isStaticInner)) =>
          val pre = lookup(outer, isStaticInner)
          pre.select(if isStatic then name else name.toTypeName)
        case None =>
          val (pkgRef, cls) = binaryName.name.lastIndexOf('/') match
            case -1 => (defn.RootPackage.packageRef, binaryName)
            case i  => (computePkg(binaryName.name.take(i)), termName(binaryName.name.drop(i + 1)))
          pkgRef.select(if isStatic then cls else cls.toTypeName)
    end computeRef

    private def computePkg(packageName: String)(using Context): PackageRef =
      val parts = packageName.split('/').map(termName).toList
      ctx.findPackageFromRoot(FullyQualifiedName(parts)).packageRef

    private def lookup(binaryName: SimpleName, isStatic: Boolean)(using Context, InnerClasses): NamedType =
      if isStatic then staticrefs.getOrElseUpdate(binaryName, computeRef(binaryName, isStatic = true).asTerm)
      else refs.getOrElseUpdate(binaryName, computeRef(binaryName, isStatic = false).asType)

    def resolve(binaryName: SimpleName)(using Context, InnerClasses): TypeRef =
      lookup(binaryName, isStatic = false).asType

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
    )(using Context): InnerClasses =
      import structure.reader

      def missingClass(binaryName: SimpleName) =
        ClassfileFormatException(s"Inner class $binaryName not found, keys: ${lookup.keys.toList}")

      def lookupDeclaration(isStatic: Boolean, name: SimpleName, binaryName: SimpleName): InnerClassDecl =
        val data = lookup.getOrElse(binaryName, throw missingClass(binaryName))
        InnerClassDecl(data, name, if isStatic then moduleClass else cls)

      val refsBuf = Map.newBuilder[SimpleName, InnerClassRef]
      val declsBuf = List.newBuilder[InnerClassDecl]
      innerClasses.use {
        reader.readInnerClasses { (name, innerBinaryName, outerBinaryName, flags) =>
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
    val reader: ClassfileReader,
    val supers: Forked[DataStream],
    val fields: Forked[DataStream],
    val methods: Forked[DataStream],
    val attributes: Forked[DataStream]
  )(using val pool: reader.ConstantPool)

  def loadScala2Class(structure: Structure, runtimeAnnotStart: Forked[DataStream])(using Context): Unit = {
    import structure.{reader, given}

    val Some(Annotation(tpe, args)) = runtimeAnnotStart.use {
      reader.readAnnotation(Set(annot.ScalaLongSignature, annot.ScalaSignature))
    }: @unchecked

    val sigBytes = tpe match {
      case annot.ScalaSignature =>
        val bytesArg = args.head.asInstanceOf[AnnotationValue.Const[pool.type]]
        pool.sigbytes(bytesArg.valueIdx)
      case annot.ScalaLongSignature =>
        val bytesArrArg = args.head.asInstanceOf[AnnotationValue.Arr[pool.type]]
        val idxs = bytesArrArg.values.map(_.asInstanceOf[AnnotationValue.Const[pool.type]].valueIdx)
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
  )(using Context, Resolver): List[InnerClassDecl] = {
    import structure.{reader, given}

    val pkg = classOwner.closestPackage

    val allRegisteredSymbols = mutable.ListBuffer.empty[Symbol]

    val cls = ClassSymbol.create(name.toTypeName, classOwner)
    allRegisteredSymbols += cls

    def privateWithin(access: AccessFlags): Option[Symbol] =
      if access.isPackagePrivate then Some(pkg) else None

    val clsFlags = structure.access.toFlags
    val clsPrivateWithin = privateWithin(structure.access)

    val moduleClass = ClassSymbol
      .create(name.withObjectSuffix.toTypeName, classOwner)
      .withTypeParams(Nil)
      .withFlags(clsFlags | Flags.ModuleClassCreationFlags, clsPrivateWithin)
      .setAnnotations(Nil)
      .withParentsDirect(defn.ObjectType :: Nil)
    allRegisteredSymbols += moduleClass

    val module = TermSymbol
      .create(name.toTermName, classOwner)
      .withDeclaredType(moduleClass.typeRef)
      .withFlags(clsFlags | Flags.ModuleValCreationFlags, clsPrivateWithin)
      .setAnnotations(Nil)
    allRegisteredSymbols += module

    def readInnerClasses(innerClasses: Forked[DataStream]): InnerClasses =
      InnerClasses.parse(cls, moduleClass, structure, innerLookup, innerClasses)

    val innerClassesStrict = optInnerClasses.map(readInnerClasses).getOrElse(InnerClasses.Empty)
    given InnerClasses = innerClassesStrict

    def createMember(name: SimpleName, baseFlags: FlagSet, access: AccessFlags): TermSymbol =
      val flags = baseFlags | access.toFlags
      val owner = if flags.is(Flags.Static) then moduleClass else cls
      val sym = TermSymbol.create(name, owner).withFlags(flags, privateWithin(access))
      sym.setAnnotations(Nil) // TODO Read Java annotations on fields and methods
      allRegisteredSymbols += sym
      sym

    def loadMembers(): IArray[(TermSymbol, SigOrDesc)] =
      val buf = IArray.newBuilder[(TermSymbol, SigOrDesc)]
      structure.fields.use {
        reader.readFields { (name, sigOrDesc, access) =>
          buf += createMember(name, EmptyFlagSet, access) -> sigOrDesc
        }
      }
      structure.methods.use {
        reader.readMethods { (name, sigOrDesc, access) =>
          buf += createMember(name, Method, access) -> sigOrDesc
        }
      }
      buf.result()
    end loadMembers

    def initParents(): Unit =
      def binaryName(cls: ConstantInfo.Class[pool.type]) =
        pool.utf8(cls.nameIdx)
      val parents = classSig match
        case SigOrSupers.Sig(sig) =>
          JavaSignatures.parseSignature(cls, sig, allRegisteredSymbols) match
            case mix: AndType => mix.parts
            case sup          => sup :: Nil
        case SigOrSupers.Supers =>
          structure.supers.use {
            val superClass = reader.readSuperClass().map(binaryName)
            val interfaces = reader.readInterfaces().map(binaryName)
            Descriptors.parseSupers(cls, superClass, interfaces)
          }
      end parents
      cls.withParentsDirect(parents)
    end initParents

    cls.withFlags(clsFlags, clsPrivateWithin)
    cls.setAnnotations(Nil) // TODO Read Java annotations on classes
    initParents()

    for (sym, sigOrDesc) <- loadMembers() do
      sigOrDesc match
        case SigOrDesc.Desc(desc) => sym.withDeclaredType(Descriptors.parseDescriptor(sym, desc))
        case SigOrDesc.Sig(sig)   => sym.withDeclaredType(JavaSignatures.parseSignature(sym, sig, allRegisteredSymbols))

    for sym <- allRegisteredSymbols do sym.checkCompleted()

    innerClasses.declarations
  }

  private def parse(classRoot: ClassData, structure: Structure)(using Context): ClassKind = {
    import structure.{reader, given}

    def process(attributesStream: Forked[DataStream]): ClassKind =
      var runtimeAnnotStart: Forked[DataStream] | Null = null
      var innerClassesStart: Option[Forked[DataStream]] = None
      var sigOrNull: String | Null = null
      var isScala = false
      var isTASTY = false
      var isScalaRaw = false
      attributesStream.use {
        reader.scanAttributes {
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
            if !(isScala || isScalaRaw || isTASTY) then sigOrNull = data.fork.use(reader.readSignature)
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
    end process

    process(structure.attributes)
  }

  private def structure(reader: ClassfileReader)(using reader.ConstantPool)(using DataStream): Structure = {
    val access = reader.readAccessFlags()
    val thisClass = reader.readThisClass()
    val supers = data.forkAndSkip {
      data.skip(2) // superclass
      data.skip(2 * data.readU2()) // interfaces
    }
    Structure(
      access = access,
      binaryName = reader.pool.utf8(thisClass.nameIdx),
      reader = reader,
      supers = supers,
      fields = reader.skipFields(),
      methods = reader.skipMethods(),
      attributes = reader.skipAttributes()
    )
  }

  private def toplevel(classOwner: DeclaringSymbol, classRoot: ClassData)(using Context): Structure = {
    def headerAndStructure(reader: ClassfileReader)(using DataStream) = {
      reader.acceptHeader(classOwner, classRoot)
      structure(reader)(using reader.readConstantPool())
    }

    ClassfileReader.unpickle(classRoot)(headerAndStructure)
  }

  def readKind(classOwner: DeclaringSymbol, classRoot: ClassData)(using Context): ClassKind =
    parse(classRoot, toplevel(classOwner, classRoot))

}
