package tastyquery.reader

import tastyquery.ast.Names.{nme, *}
import tastyquery.ast.{ParamSig, Signature, TermSig, TypeLenSig}
import tastyquery.reader.TreeUnpickler
import tastyquery.unsafe

import dotty.tools.tasty.{TastyBuffer, TastyFormat, TastyHeaderUnpickler, TastyReader}
import TastyBuffer.{Addr, NameRef}
import TastyFormat.NameTags

import scala.collection.mutable

object TastyUnpickler {

  abstract class SectionUnpickler[R](val name: String) {
    def unpickle(reader: TastyReader, nameAtRef: NameTable): R
  }

  class TreeSectionUnpickler(posUnpickler: Option[PositionUnpickler])
  extends SectionUnpickler[TreeUnpickler]("ASTs") {
    def unpickle(reader: TastyReader, nameAtRef: NameTable): TreeUnpickler =
      new TreeUnpickler(reader, nameAtRef, posUnpickler)
  }

  class PositionSectionUnpickler extends SectionUnpickler[PositionUnpickler]("Positions") {
    def unpickle(reader: TastyReader, nameAtRef: NameTable): PositionUnpickler =
      new PositionUnpickler(reader, nameAtRef)
  }

  class NameTable extends (NameRef => TermName) {
    private val names = new mutable.ArrayBuffer[TermName]

    def add(name: TermName): mutable.ArrayBuffer[TermName] = names += name

    def apply(ref: NameRef): TermName = names(ref.index)

    def contents: Iterable[TermName] = names
  }

}

import tastyquery.reader.TastyUnpickler.*

class TastyUnpickler(reader: TastyReader) {

  import reader.*

  def this(bytes: IArray[Byte]) =
    // ok to use as Array because TastyReader is readOnly
    this(new TastyReader(unsafe.asByteArray(bytes)))

  private val sectionReader = new mutable.HashMap[String, TastyReader]
  /** Reserved for PositionUnpickler */
  private val sectionReaderCloned = new mutable.HashMap[String, TastyReader]
  val nameAtRef: NameTable = new NameTable

  private def readName(): TermName = nameAtRef(readNameRef())

  private def readString(): String = readName().toString

  private def readParamSig(): ParamSig = {
    val ref = readInt()
    if (ref < 0)
      TypeLenSig(ref.abs)
    else
      TermSig(nameAtRef(new NameRef(ref)).toTypeName)
  }

  private def readNameContents(): TermName = {
    val tag = readByte()
    val length = readNat()
    val start: Addr = reader.currentAddr
    val end: Addr = start + length
    val result = tag match {
      case NameTags.UTF8 =>
        reader.goto(end)
        termName(bytes, start.index, length)
      case NameTags.QUALIFIED | NameTags.EXPANDED | NameTags.EXPANDPREFIX =>
        new QualifiedName(tag, readName(), readName().asSimpleName)
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
        val result = readName().toTypeName
        val paramsSig = reader.until(end)(readParamSig())
        val sig = Signature(paramsSig, result)
        new SignedName(original, sig, target)
      case NameTags.SUPERACCESSOR | NameTags.INLINEACCESSOR =>
        new PrefixedName(tag, readName())
      case NameTags.BODYRETAINER | NameTags.OBJECTCLASS =>
        new SuffixedName(tag, readName())
      case _ => throw new UnsupportedOperationException(s"unexpected tag: $tag")
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

  def unpickle[R](sec: SectionUnpickler[R]): Option[R] =
    for (reader <- sectionReader.get(sec.name)) yield sec.unpickle(reader, nameAtRef)

  def bytes: Array[Byte] = reader.bytes
}
