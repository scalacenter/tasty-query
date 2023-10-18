package tastyquery.reader.tasties

import scala.collection.mutable

import dotty.tools.tasty.TastyBuffer.{Addr, NameRef}
import dotty.tools.tasty.TastyFormat.NameTags
import dotty.tools.tasty.{TastyHeaderUnpickler, TastyReader}

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Names.*
import tastyquery.Signatures.*

import tastyquery.reader.{ReaderContext, UTF8Utils}

private[reader] object TastyUnpickler {

  abstract class SectionUnpickler[R](val name: String) {
    def unpickle(filename: String, reader: TastyReader, nameAtRef: NameTable)(using ReaderContext): R
  }

  class TreeSectionUnpickler(posUnpickler: Option[PositionUnpickler]) extends SectionUnpickler[TreeUnpickler]("ASTs") {
    def unpickle(filename: String, reader: TastyReader, nameAtRef: NameTable)(using ReaderContext): TreeUnpickler =
      new TreeUnpickler(filename, reader, nameAtRef, posUnpickler)
  }

  class PositionSectionUnpickler extends SectionUnpickler[PositionUnpickler]("Positions") {
    def unpickle(filename: String, reader: TastyReader, nameAtRef: NameTable)(using ReaderContext): PositionUnpickler =
      new PositionUnpickler(reader, nameAtRef)
  }

  final class NameTable {
    private[TastyUnpickler] type EitherName = TermName | FullyQualifiedName

    private val names = new mutable.ArrayBuffer[EitherName]

    private[TastyUnpickler] def add(name: EitherName): Unit = names += name

    private[TastyUnpickler] def apply(ref: NameRef): EitherName =
      names(ref.index)

    def simple(ref: NameRef): TermName =
      apply(ref) match
        case name: TermName =>
          name
        case name: FullyQualifiedName =>
          throw TastyFormatException(s"Expected TermName but got ${name.toDebugString}")

    def fullyQualified(ref: NameRef): FullyQualifiedName =
      apply(ref) match
        case name: FullyQualifiedName =>
          name.path match
            case nme.RootPackageName :: Nil =>
              FullyQualifiedName.rootPackageName
            case _ =>
              name
        case nme.RootPackageName =>
          FullyQualifiedName.rootPackageName
        case name: TermName =>
          FullyQualifiedName(name :: Nil)
  }

}

private[reader] class TastyUnpickler(reader: TastyReader) {
  import TastyUnpickler.*

  import reader.*

  def this(bytes: Array[Byte]) =
    // ok to use as Array because TastyReader is readOnly
    this(new TastyReader(bytes))

  private val sectionReader = new mutable.HashMap[String, TastyReader]
  val nameAtRef: NameTable = new NameTable

  private def readName(): TermName = nameAtRef.simple(readNameRef())

  private def readFullyQualifiedName(): FullyQualifiedName = nameAtRef.fullyQualified(readNameRef())

  private def readEitherName(): nameAtRef.EitherName = nameAtRef(readNameRef())

  private def readString(): String = readName().toString

  private def readParamSig(): ParamSig = {
    val ref = readInt()
    if (ref < 0)
      ParamSig.TypeLen(ref.abs)
    else
      ParamSig.Term(nameAtRef.fullyQualified(new NameRef(ref)).mapLast(_.toTypeName))
  }

  private def readNameContents(): nameAtRef.EitherName = {
    val tag = readByte()
    val length = readNat()
    val start: Addr = reader.currentAddr
    val end: Addr = start + length
    val result: nameAtRef.EitherName = tag match {
      case NameTags.UTF8 =>
        reader.goto(end)
        termName(UTF8Utils.decode(bytes, start.index, length))
      case NameTags.QUALIFIED =>
        val qual = readFullyQualifiedName()
        val item = readName()
        FullyQualifiedName(qual.path :+ item)
      case NameTags.EXPANDED =>
        ExpandedName(readName(), readName().asSimpleName)
      case NameTags.EXPANDPREFIX =>
        ExpandPrefixName(readName(), readName().asSimpleName)
      case NameTags.UNIQUE =>
        val separator = readName().toString
        val num = readNat()
        val originals = reader.until(end)(readName())
        val original = if (originals.isEmpty) nme.EmptyTermName else originals.head
        new UniqueName(separator, original, num)
      case NameTags.DEFAULTGETTER =>
        new DefaultGetterName(readName(), readNat())
      case NameTags.SIGNED | NameTags.TARGETSIGNED =>
        val original = readName()
        val target = if (tag == NameTags.TARGETSIGNED) readName() else original
        val result = readFullyQualifiedName().mapLast(_.toTypeName)
        val paramsSig = reader.until(end)(readParamSig())
        val sig = Signature(paramsSig, result)
        new SignedName(original, sig, target)
      case NameTags.SUPERACCESSOR =>
        SuperAccessorName(readName())
      case NameTags.INLINEACCESSOR =>
        InlineAccessorName(readName())
      case NameTags.BODYRETAINER =>
        BodyRetainerName(readName())
      case NameTags.OBJECTCLASS =>
        readEitherName() match
          case simple: TermName              => simple.withObjectSuffix
          case qualified: FullyQualifiedName => qualified.mapLast(_.asSimpleName.withObjectSuffix)
      case _ => throw TastyFormatException(s"unexpected tag: $tag")
    }
    assert(reader.currentAddr == end, s"bad name $result $start ${reader.currentAddr} $end")
    result
  }

  new TastyHeaderUnpickler(reader).readHeader()

  locally {
    reader.until(readEnd())(nameAtRef.add(readNameContents()))
    while (!isAtEnd) {
      val secName = readString()
      val secEnd: Addr = readEnd()
      sectionReader(secName) = new TastyReader(bytes, currentAddr.index, secEnd.index, currentAddr.index)
      reader.goto(secEnd)
    }
  }

  def unpickle[R](filename: String, sec: SectionUnpickler[R])(using ReaderContext): Option[R] =
    for (reader <- sectionReader.get(sec.name)) yield sec.unpickle(filename, reader, nameAtRef)

  def bytes: Array[Byte] = reader.bytes
}
