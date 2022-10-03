package tastyquery.reader.classfiles

import tastyquery.Classpaths.*
import tastyquery.Contexts.*
import tastyquery.Flags
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Types.*

import tastyquery.reader.pickles.{Unpickler, PickleReader}

import tastyquery.util.Forked
import tastyquery.util.syntax.chaining.given

import ClassfileReader.*

object ClassfileParser {

  enum ClassKind:
    case Scala2(structure: Structure, runtimeAnnotStart: Forked[DataStream])
    case Java(structure: Structure, classSig: SigOrSupers)
    case TASTy
    case Artifact

  class Structure(
    val binaryName: SimpleName,
    val reader: ClassfileReader,
    val supers: Forked[DataStream],
    val fields: Forked[DataStream],
    val methods: Forked[DataStream],
    val attributes: Forked[DataStream]
  )(using val pool: reader.ConstantPool)

  def loadScala2Class(structure: Structure, runtimeAnnotStart: Forked[DataStream])(
    using Context
  ): Either[PickleReader.BadSignature, Unit] = {
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

  def loadJavaClass(classOwner: DeclaringSymbol, name: SimpleName, structure: Structure, classSig: SigOrSupers)(
    using Context
  ): Either[ReadException, Unit] = {
    import structure.{reader, given}

    val cls = ClassSymbol.create(name.toTypeName, classOwner)

    val moduleClass = ClassSymbol
      .create(name.withObjectSuffix.toTypeName, classOwner)
      .withTypeParams(Nil, Nil)
      .withFlags(Flags.ModuleClassCreationFlags)
    moduleClass.withParentsDirect(ObjectType :: Nil)

    val module = TermSymbol
      .create(name.toTermName, classOwner)
      .withDeclaredType(moduleClass.typeRef)
      .withFlags(Flags.ModuleValCreationFlags)

    def loadFields(fields: Forked[DataStream]): IndexedSeq[(TermSymbol, SigOrDesc)] =
      fields.use {
        val buf = IndexedSeq.newBuilder[(TermSymbol, SigOrDesc)]
        reader.readFields { (name, sigOrDesc) =>
          val sym = TermSymbol.create(name, cls).withFlags(Flags.EmptyFlagSet)
          buf += sym -> sigOrDesc
        }
        buf.result()
      }

    def loadMethods(methods: Forked[DataStream]): IndexedSeq[(TermSymbol, SigOrDesc)] =
      methods.use {
        val buf = IndexedSeq.newBuilder[(TermSymbol, SigOrDesc)]
        reader.readMethods { (name, sigOrDesc) =>
          val sym = TermSymbol.create(name, cls).withFlags(Flags.Method)
          buf += sym -> sigOrDesc
        }
        buf.result()
      }

    def initParents(): Unit =
      def binaryName(cls: ConstantInfo.Class[pool.type]) =
        pool.utf8(cls.nameIdx).name
      val parents = classSig match
        case SigOrSupers.Sig(sig) =>
          JavaSignatures.parseSignature(cls, sig) match
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

    ClassfileReader.read {
      // TODO: move static methods to companion object
      cls.withFlags(Flags.EmptyFlagSet) // TODO: read flags
      initParents()
      val members = loadFields(structure.fields) ++ loadMethods(structure.methods)
      for (sym, sigOrDesc) <- members do
        sigOrDesc match
          case SigOrDesc.Desc(desc) => sym.withDeclaredType(Descriptors.parseDescriptor(sym, desc))
          case SigOrDesc.Sig(sig)   => sym.withDeclaredType(JavaSignatures.parseSignature(sym, sig))
    }
  }

  private def parse(classRoot: ClassData, structure: Structure)(using Context): ClassKind = {
    import structure.{reader, given}

    def process(attributesStream: Forked[DataStream]): ClassKind =
      var runtimeAnnotStart: Forked[DataStream] | Null = null
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
          case _ =>
            false
        }
        isScalaRaw &= !isTASTY
      }
      if isScala then
        val annots = runtimeAnnotStart
        if annots != null then ClassKind.Scala2(structure, annots)
        else throw ReadException(s"class file for ${classRoot.binaryName} is a scala 2 class, but has no annotations")
      else if isTASTY then ClassKind.TASTy
      else if isScalaRaw then ClassKind.Artifact
      else
        val sig = sigOrNull
        val classSig = if sig != null then SigOrSupers.Sig(sig) else SigOrSupers.Supers
        ClassKind.Java(structure, classSig)
    end process

    process(structure.attributes)
  }

  private def structure(reader: ClassfileReader)(using reader.ConstantPool)(using DataStream): Structure = {
    val access = reader.readAccessFlags()
    val thisClass = reader.readThisClass()
    val supers = data.fork andThen {
      data.skip(2) // superclass
      data.skip(2 * data.readU2()) // interfaces
    }
    Structure(
      binaryName = reader.pool.utf8(thisClass.nameIdx),
      reader = reader,
      supers = supers,
      fields = reader.skipFields(),
      methods = reader.skipMethods(),
      attributes = reader.skipAttributes()
    )
  }

  private def toplevel(classRoot: ClassData)(using Context): Structure = {
    def headerAndStructure(reader: ClassfileReader)(using DataStream) = {
      reader.acceptHeader()
      structure(reader)(using reader.readConstantPool())
    }

    ClassfileReader.unpickle(classRoot)(headerAndStructure)
  }

  def readKind(classRoot: ClassData)(using Context): Either[ReadException, ClassKind] =
    ClassfileReader.read(parse(classRoot, toplevel(classRoot)))

}
