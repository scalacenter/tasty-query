package tastyquery.reader.classfiles

import tastyquery.util.Forked
import tastyquery.ast.Names.attr
import tastyquery.ast.Names.annot
import tastyquery.ast.Names.SimpleName
import tastyquery.ast.Symbols.RegularSymbolFactory
import tastyquery.Contexts.{ClassContext, clsCtx}
import tastyquery.reader.pickles.{Unpickler, PickleReader}

import Classpaths.ClassData
import ClassfileReader.{DataStream, ReadException, Annotation, AnnotationValue, data}

object ClassfileParser {

  enum ClassKind:
    case Scala2(structure: Structure, runtimeAnnotStart: Forked[DataStream])
    case Java(structure: Structure)
    case TASTy
    case Artifact

  class Structure(
    val binaryName: SimpleName,
    val reader: ClassfileReader,
    val fields: Forked[DataStream],
    val methods: Forked[DataStream],
    val attributes: Forked[DataStream]
  )(using val pool: reader.ConstantPool)

  def loadScala2Class(structure: Structure, runtimeAnnotStart: Forked[DataStream])(
    using ClassContext
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

  def loadJavaClass(structure: Structure)(using ClassContext): Either[ReadException, Unit] = {
    import structure.{reader, given}

    def loadFields(fields: Forked[DataStream]): Unit =
      fields.use {
        reader.readFields { name =>
          clsCtx.createSymbol(name, RegularSymbolFactory, addToDecls = true)
        }
      }

    def loadMethods(methods: Forked[DataStream]): Unit =
      methods.use {
        reader.readMethods { name =>
          clsCtx.createSymbol(name, RegularSymbolFactory, addToDecls = true)
        }
      }

    ClassfileReader.read {
      loadFields(structure.fields)
      loadMethods(structure.methods) // TODO: move static methods to companion object
      clsCtx.classRoot.initialised = true
      clsCtx.moduleClassRoot.initialised = true
    }
  }

  private def parse(classRoot: ClassData, structure: Structure)(using ClassContext): ClassKind = {
    import structure.{reader, given}

    def process(attributesStream: Forked[DataStream]): ClassKind =
      var runtimeAnnotStart: Forked[DataStream] | Null = null
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
          case _ =>
            false
        }
        isScalaRaw &= !isTASTY
      }
      if isScala then
        println(s"class file for ${structure.binaryName} is a scala 2 class")
        val annots = runtimeAnnotStart
        if annots != null then ClassKind.Scala2(structure, annots)
        else throw ReadException(s"class file for ${classRoot.simpleName} is a scala 2 class, but has no annotations")
      else if isTASTY then
        println(s"class file for ${structure.binaryName} is a tasty class, ignoring")
        ClassKind.TASTy
      else if isScalaRaw then
        println(s"class file for ${structure.binaryName} is a scala compiler artifact, ignoring")
        ClassKind.Artifact
      else
        println(s"class file for ${structure.binaryName} is a java class")
        ClassKind.Java(structure)
    end process

    process(structure.attributes)
  }

  private def structure(reader: ClassfileReader)(using reader.ConstantPool)(using DataStream): Structure = {
    val access = reader.readAccessFlags()
    val thisClass = reader.readThisClass()
    val superClass = reader.readSuperClass()
    val interfaces = reader.readInterfaces()
    Structure(
      binaryName = reader.pool.utf8(thisClass.nameIdx),
      reader,
      fields = reader.skipFields(),
      methods = reader.skipMethods(),
      attributes = reader.skipAttributes()
    )
  }

  private def toplevel(classRoot: ClassData)(using ClassContext): Structure = {
    val root = clsCtx.classRoot
    println(s"loading class file for ${root.enclosingDecl.name}.${root.name} with ${classRoot.bytes.size} bytes")

    def headerAndStructure(reader: ClassfileReader)(using DataStream) = {
      reader.acceptHeader()
      structure(reader)(using reader.readConstantPool())
    }

    ClassfileReader.unpickle(classRoot)(headerAndStructure)
  }

  def readKind(classRoot: ClassData)(using ClassContext): Either[ReadException, ClassKind] =
    ClassfileReader.read(parse(classRoot, toplevel(classRoot)))

}