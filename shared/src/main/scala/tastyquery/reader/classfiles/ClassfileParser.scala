package tastyquery.reader.classfiles

import tastyquery.util.Forked
import tastyquery.ast.Names.attr
import tastyquery.ast.Symbols.RegularSymbolFactory
import tastyquery.Contexts.{ClassContext, clsCtx}

import ClassfileReader.{DataStream, ReadException, data}
import Classpaths.ClassData
import tastyquery.ast.Names.SimpleName

object ClassfileParser {

  class Structure(
    val binaryName: SimpleName,
    val reader: ClassfileReader,
    val fields: Forked[DataStream],
    val methods: Forked[DataStream],
    val attributes: Forked[DataStream]
  )(using val pool: reader.ConstantPool)

  def loadJavaClass(structure: Structure)(using ClassContext): Unit = {
    import structure.{reader, given}

    def loadFields(fields: Forked[DataStream]): Unit =
      fields.use {
        reader.readFields { name =>
          clsCtx.createSymbolIfNew(name, RegularSymbolFactory, addToDecls = true)
        }
      }

    def loadMethods(methods: Forked[DataStream]): Unit =
      methods.use {
        reader.readMethods { name =>
          clsCtx.createSymbolIfNew(name, RegularSymbolFactory, addToDecls = true)
        }
      }

    loadFields(structure.fields)
    loadMethods(structure.methods)
  }

  def parse(classRoot: ClassData, structure: Structure)(using ClassContext): Unit = {
    import structure.{reader, given}

    def process(attributesStream: Forked[DataStream]): Unit = {
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
      if isScala then {
        println(s"class file for ${structure.binaryName} is a scala 2 class, ignoring")
      } else if isTASTY then {
        println(s"class file for ${structure.binaryName} is a tasty class, ignoring")
      } else if isScalaRaw then {
        println(s"class file for ${structure.binaryName} is a scala compiler artifact, ignoring")
      } else {
        println(s"class file for ${structure.binaryName} is a java class")
        loadJavaClass(structure)
      }
    }

    process(structure.attributes)
  }

  def structure(reader: ClassfileReader)(using reader.ConstantPool)(using DataStream) = {
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

  def toplevel(classRoot: ClassData)(using ClassContext): Structure = {
    val root = clsCtx.owner
    println(s"loading class file for ${root.owner.nn.name}.${root.name} with ${classRoot.bytes.size} bytes")

    def headerAndStructure(reader: ClassfileReader)(using DataStream) = {
      reader.acceptHeader()
      structure(reader)(using reader.readConstantPool())
    }

    ClassfileReader.unpickle(classRoot)(headerAndStructure)
  }

  def loadInfo(classRoot: ClassData)(using ClassContext): Either[ReadException, Unit] =
    ClassfileReader.read {
      ClassfileParser.parse(classRoot, ClassfileParser.toplevel(classRoot))
    }

}
