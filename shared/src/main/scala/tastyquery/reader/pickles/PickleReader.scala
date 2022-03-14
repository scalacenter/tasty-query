package tastyquery.reader.pickles

import tastyquery.ast.Names.{TermName, termName, TypeName, typeName, nme}
import tastyquery.ast.Symbols.{Symbol, NoSymbol}
import tastyquery.Contexts.{ClassContext, clsCtx}

import PickleReader.*
import PickleFormat.*
import tastyquery.ast.Names.Name
import tastyquery.ast.Symbols.RegularSymbolFactory
import tastyquery.ast.Symbols.ClassSymbolFactory
import tastyquery.ast.Symbols.ClassSymbol

import tastyquery.util.syntax.chaining.given
import tastyquery.ast.Symbols.DeclaringSymbol

class PickleReader {
  opaque type Entries = Array[AnyRef | Null]
  opaque type Index = IArray[Int]

  class Structure(using val myEntries: Entries, val myIndex: Index)

  extension (i: Index)
    inline def loopWithIndices(inline op: (Int, Int) => Unit): Unit = {
      val limit = i.length
      var j = 0
      while j < limit do {
        op(i(j), j)
        j += 1
      }
    }

  def readStructure()(using PklStream): Structure = {
    checkVersion()
    val index = pkl.readIndex()
    val entries = new Array[AnyRef | Null](index.length)

    given Index = index
    given Entries = entries

    println("read pickles structure")
    Structure()
  }

  private def checkVersion()(using PklStream): Unit = {
    val major = pkl.readNat()
    val minor = pkl.readNat()
    if (major != MajorVersion || minor > MinorVersion)
      throw java.io.IOException(s"Bad pickles version, expected: $MajorVersion.$MinorVersion, found: $major.$minor")
  }

  def errorBadSignature(msg: String): Nothing =
    throw PickleReader.BadSignature(msg)

  private def at[T <: AnyRef](i: Int)(op: PklStream ?=> T)(using PklStream, Entries, Index): T = {
    val tOpt = entries(i).asInstanceOf[T | Null]
    if tOpt == null then {
      val res = pkl.unsafeFork(index(i))(op)
      assert(entries(i) == null, entries(i))
      entries(i) = res
      res
    } else tOpt
  }

  def readNameRef()(using PklStream, Entries, Index): Name = at(pkl.readNat())(readName())

  def readName()(using PklStream): Name = {
    val tag = pkl.readByte()
    val len = pkl.readNat()
    tag match {
      case TERMname => pkl.readTermName(len)
      case TYPEname => pkl.readTypeName(len)
      case _        => errorBadSignature("bad name tag: " + tag)
    }
  }

  def readSymbol()(using ClassContext, PklStream, Entries, Index): Symbol = readDisambiguatedSymbol(alwaysTrue)()

  def readSymbolRef()(using ClassContext, PklStream, Entries, Index): Symbol =
    // Note: in dotty this call to `at` is inlined manually.
    at(pkl.readNat())(readSymbol())

  private def readDisambiguatedSymbol(p: Symbol => Boolean)()(using ClassContext, PklStream, Entries, Index): Symbol = {
    // val start = indexCoord(readIndex) // no need yet to record the position of symbols
    val tag = pkl.readByte()
    val end = pkl.readEnd()
    def atEnd(using PklStream) = pkl.atOffset(end)

    def readExtSymbol(): Symbol =
      ???

    tag match {
      case NONEsym                 => return NoSymbol
      case EXTref | EXTMODCLASSref =>
        // return readExtSymbol()
        println("skipped external symbol")
        return NoSymbol
      case _ =>
    }

    // symbols that were pickled with Pickler.writeSymInfo
    val nameref = pkl.readNat()
    val name = at(nameref)(readName())
    val owner = readSymbolRef()

    println(s"readSymbol(${name.toDebugString}, $owner)")

    val flagsRaw = pkl.readLongNat() // TODO: Decode into flags

    val (privateWithin, infoRef) = {
      val ref = pkl.readNat()
      if (!isSymbolRef(ref)) (NoSymbol, ref)
      else {
        val pw = at(ref)(readSymbol())
        (pw, pkl.readNat())
      }
    }

    def nameMatches(rootName: Name) = name == rootName
    def isClassRoot = nameMatches(clsCtx.classRoot.name) //&& (owner == classRoot.owner) && !flags.is(ModuleClass)
    def isModuleClassRoot = nameMatches(
      clsCtx.moduleClassRoot.name
    ) //&& (owner == moduleClassRoot.owner) && flags.is(Module)
    def isModuleRoot = nameMatches(clsCtx.moduleRoot.name) //&& (owner == moduleClassRoot.owner) && flags.is(Module)

    def finishSym(sym: Symbol): Symbol = {
      // TODO: enter in scope
      sym match {
        case sym: ClassSymbol =>
        case sym =>
          sym.outer match {
            case scope: DeclaringSymbol => scope.addDecl(sym)
            case _                      =>
          }
      }
      sym
    }

    finishSym(tag match {
      case TYPEsym | ALIASsym =>
        var name1 = name.toTypeName
        // var flags1 = flags
        // if (flags.is(TypeParam)) flags1 |= owner.typeParamCreationFlags
        // newSymbol(owner, name1, flags1, localMemberUnpickler, privateWithin, coord = start)

        // TODO: clsCtx at owner
        clsCtx.createSymbol(name1, RegularSymbolFactory, addToDecls = false)
      case CLASSsym =>
        if isClassRoot then clsCtx.classRoot useWith { _.initialised = true }
        else if isModuleClassRoot then clsCtx.moduleClassRoot useWith { _.initialised = true }
        else clsCtx.createSymbol(name.toTypeName, ClassSymbolFactory, addToDecls = false)
      case VALsym =>
        clsCtx.createSymbol(name.toTermName, RegularSymbolFactory, addToDecls = false)
      case MODULEsym =>
        if isModuleRoot then {
          clsCtx.moduleRoot
        } else {
          ???
        }
      case _ =>
        errorBadSignature("bad symbol tag: " + tag)
    })
  }

  def missingSymbolEntry(index: Int)(using PklStream, Entries, Index): Boolean =
    missingEntry(index) && isSymbolEntry(index)

  def missingEntry(index: Int)(using Entries): Boolean =
    entries(index) == null

  def addEntry[A <: AnyRef](index: Int, ref: A)(using Entries): Unit =
    entries(index) = ref

  def isSymbolEntry(i: Int)(using PklStream, Entries, Index): Boolean = {
    val tag = pkl.bytes(index(i)).toInt
    (firstSymTag <= tag && tag <= lastSymTag &&
    (tag != CLASSsym || !isRefinementSymbolEntry(i)))
  }

  def isRefinementSymbolEntry(i: Int)(using PklStream, Entries, Index): Boolean =
    pkl.unsafeFork(index(i)) {
      val tag = pkl.readByte().toInt
      assert(tag == CLASSsym)
      pkl.readNat() // read length
      val result = readNameRef() == nme.RefinementClass
      result
    }

  def isSymbolRef(i: Int)(using PklStream, Index): Boolean = {
    val tag = pkl.bytes(index(i))
    (firstSymTag <= tag && tag <= lastExtSymTag)
  }
}

object PickleReader {

  def pkl(using pkl: PklStream): pkl.type = pkl
  def index[I <: PickleReader#Index & Singleton](using index: I): index.type = index
  def entries[E <: PickleReader#Entries & Singleton](using entries: E): entries.type = entries

  private val alwaysTrue: Any => Boolean = _ => true

  final class BadSignature(message: String) extends Exception(message)

  object PklStream {
    def read[T](bytes: IArray[Byte])(op: PklStream ?=> T): T =
      op(using PklStream(PickleBuffer(bytes, from = 0)))
  }

  final class PklStream private (in: PickleBuffer) {
    export in.readByte
    export in.readNat
    export in.readLongNat
    export in.createIndex as readIndex
    export in.readIndex as currentOffset
    export in.bytes

    def readEnd(): Int = readNat() + in.readIndex
    def atOffset(offset: Int): Boolean = in.readIndex == offset

    def readTermName(length: Int): TermName =
      termName(in.bytes, in.readIndex, length)

    def readTypeName(length: Int): TypeName =
      typeName(in.bytes, in.readIndex, length)

    final inline def unsafeFork[T](offset: Int)(inline op: PklStream ?=> T): T = {
      val saved = in.readIndex
      try {
        in.readIndex = offset
        op(using this)
      } finally in.readIndex = saved
    }

  }

}
