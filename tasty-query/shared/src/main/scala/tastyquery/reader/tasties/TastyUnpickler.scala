package tastyquery.reader.tasties

import scala.collection.mutable

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Names.*
import tastyquery.Signatures.*

import tastyquery.reader.{ReaderContext, UTF8Utils}

import TastyFormat.NameTags
import TastyReader.{Addr, NameRef}

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
    private[TastyUnpickler] type EitherName = TermName | SignatureName

    private val names = new mutable.ArrayBuffer[EitherName]

    private[TastyUnpickler] def add(name: EitherName): Unit = names += name

    private[TastyUnpickler] def apply(ref: NameRef): EitherName =
      names(ref.index)

    def simple(ref: NameRef): TermName =
      apply(ref) match
        case name: TermName =>
          name
        case name: SignatureName =>
          throw TastyFormatException(s"Expected TermName but got ${name.toDebugString}")

    def packageFullName(ref: NameRef): PackageFullName =
      def invalid(actualDebugString: String): Nothing =
        throw TastyFormatException(s"Excepted a package full name but got $actualDebugString")

      apply(ref) match
        case name: SignatureName =>
          name.items match
            case nme.UserLandRootPackageName :: Nil =>
              PackageFullName.rootPackageName
            case items =>
              val path = items.map {
                case simpleName: SimpleName => simpleName
                case _: ObjectClassName     => invalid(name.toDebugString)
              }
              PackageFullName(path)
        case nme.UserLandRootPackageName =>
          PackageFullName.rootPackageName
        case name: SimpleName =>
          PackageFullName(name :: Nil)
        case name: TermName =>
          invalid(name.toDebugString)
    end packageFullName

    def signatureName(ref: NameRef): SignatureName =
      apply(ref) match
        case name: SignatureName =>
          name
        case name: SignatureNameItem =>
          SignatureName(name :: Nil)
        case name: TermName =>
          throw TastyFormatException(s"Expected a signature name but got ${name.toDebugString}")
    end signatureName
  }
}

private[reader] class TastyUnpickler(reader: TastyReader) {
  import TastyUnpickler.*

  import reader.*

  def this(bytes: IArray[Byte]) =
    // ok to use as Array because TastyReader is readOnly
    this(new TastyReader(bytes.unsafeArray))

  private val sectionReader = new mutable.HashMap[String, TastyReader]
  val nameAtRef: NameTable = new NameTable

  private def readName(): TermName = nameAtRef.simple(readNameRef())

  private def readUnsignedName(): UnsignedTermName = readName() match
    case name: UnsignedTermName =>
      name
    case name: SignedName =>
      throw TastyFormatException(s"Expected an unsigned name item but got ${name.toDebugString}")
  end readUnsignedName

  private def readSimpleName(): SimpleName = readName() match
    case name: SimpleName =>
      name
    case name =>
      throw TastyFormatException(s"Expected a simple name but got ${name.toDebugString}")
  end readSimpleName

  private def readSignatureNameItem(): SignatureNameItem = readName() match
    case name: SignatureNameItem =>
      name
    case name =>
      throw TastyFormatException(s"Expected a signature name item but got ${name.toDebugString}")
  end readSignatureNameItem

  private def readPackageFullName(): PackageFullName = nameAtRef.packageFullName(readNameRef())

  private def readSignatureName(): SignatureName = nameAtRef.signatureName(readNameRef())

  private def readEitherName(): nameAtRef.EitherName = nameAtRef(readNameRef())

  private def readString(): String = readName().toString

  private def readParamSig(): ParamSig = {
    val ref = readInt()
    if (ref < 0)
      ParamSig.TypeLen(ref.abs)
    else
      ParamSig.Term(nameAtRef.signatureName(new NameRef(ref)))
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
        val qual = readSignatureName()
        val item = readSignatureNameItem()
        qual.appendItem(item)
      case NameTags.EXPANDED =>
        ExpandedName(readUnsignedName(), readSimpleName())
      case NameTags.EXPANDPREFIX =>
        ExpandPrefixName(readUnsignedName(), readSimpleName())
      case NameTags.UNIQUE =>
        val separator = readName().toString
        val num = readNat()
        val originals = reader.until(end)(readUnsignedName())
        val original = if (originals.isEmpty) nme.EmptyTermName else originals.head
        new UniqueName(original, separator, num)
      case NameTags.DEFAULTGETTER =>
        new DefaultGetterName(readUnsignedName(), readNat())
      case NameTags.SIGNED | NameTags.TARGETSIGNED =>
        val original = readUnsignedName()
        val target = if (tag == NameTags.TARGETSIGNED) readUnsignedName() else original
        val result = readSignatureName()
        val paramsSig = reader.until(end)(readParamSig())
        val sig = Signature(paramsSig, result)
        new SignedName(original, sig, target)
      case NameTags.SUPERACCESSOR =>
        SuperAccessorName(readUnsignedName())
      case NameTags.INLINEACCESSOR =>
        InlineAccessorName(readUnsignedName())
      case NameTags.BODYRETAINER =>
        BodyRetainerName(readUnsignedName())
      case NameTags.OBJECTCLASS =>
        readEitherName() match
          case simple: SimpleName =>
            simple.withObjectSuffix
          case SignatureName(items) =>
            items.last match
              case last: SimpleName => SignatureName(items.init :+ last.withObjectSuffix)
              case last             => throw TastyFormatException(s"Invalid OBJECTCLASS of ${last.toDebugString}")
          case other: TermName =>
            throw TastyFormatException(s"Invalid OBJECTCLASS of ${other.toDebugString}")
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
