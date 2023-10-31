package tastyquery.reader.tasties

import tastyquery.Exceptions.TastyFormatException

import java.util.UUID

import TastyFormat.{MajorVersion, MinorVersion, ExperimentalVersion, header}

/** The Tasty Header consists of four fields:
  * - uuid
  *   - contains a hash of the sections of the TASTy file
  * - majorVersion
  *   - matching the TASTy format version that last broke backwards compatibility
  * - minorVersion
  *   - matching the TASTy format version that last broke forward compatibility
  * - experimentalVersion
  *   - 0 for final compiler version
  *   - positive for between minor versions and forward compatibility
  *     is broken since the previous stable version.
  * - toolingVersion
  *   - arbitrary string representing the tooling that produced the TASTy
  */
private[tasties] final case class TastyHeader(
  uuid: UUID,
  majorVersion: Int,
  minorVersion: Int,
  experimentalVersion: Int,
  toolingVersion: String
)

private[tasties] class TastyHeaderUnpickler(reader: TastyReader):
  import TastyHeaderUnpickler.*
  import reader.*

  def this(bytes: Array[Byte]) = this(new TastyReader(bytes))

  /** reads and verifies the TASTy version, extracting the UUID */
  def readHeader(): UUID =
    readFullHeader().uuid

  /** reads and verifies the TASTy version, extracting the whole header */
  def readFullHeader(): TastyHeader =
    for i <- 0 until header.length do check(readByte() == header(i), "not a TASTy file")
    val fileMajor = readNat()
    val fileMinor = readNat()
    val fileExperimental = readNat()

    val toolingVersion =
      val length = readNat()
      val start = currentAddr
      val end = start + length
      goto(end)
      new String(bytes, start.index, length)
    end toolingVersion

    val validVersion = TastyFormat.isVersionCompatible(
      fileMajor = fileMajor,
      fileMinor = fileMinor,
      fileExperimental = fileExperimental,
      compilerMajor = MajorVersion,
      compilerMinor = MinorVersion,
      compilerExperimental = ExperimentalVersion
    )

    check(
      validVersion, {
        val signature = signatureString(fileMajor, fileMinor, fileExperimental)
        val producedByAddendum = s"\nThe TASTy file was produced by $toolingVersion.$toolingAddendum"
        val msg =
          if fileExperimental != 0 then unstableAddendum
          else if fileMajor < MajorVersion then backIncompatAddendum
          else forwardIncompatAddendum
        signature + msg + producedByAddendum
      }
    )

    val uuid = new UUID(readUncompressedLong(), readUncompressedLong())
    new TastyHeader(uuid, fileMajor, fileMinor, fileExperimental, toolingVersion)
  end readFullHeader

  def isAtEnd: Boolean = reader.isAtEnd

  private def check(cond: Boolean, msg: => String): Unit =
    if !cond then throw new TastyFormatException(msg)
end TastyHeaderUnpickler

private[tasties] object TastyHeaderUnpickler:
  private def toolingAddendum: String =
    if ExperimentalVersion > 0 then "\nNote that your tooling is currently using an unstable TASTy version."
    else ""

  private def signatureString(fileMajor: Int, fileMinor: Int, fileExperimental: Int): String =
    def showMinorVersion(min: Int, exp: Int): String =
      val expStr = if exp == 0 then "" else s" [unstable release: $exp]"
      s"$min$expStr"

    val minorVersion = showMinorVersion(MinorVersion, ExperimentalVersion)
    val fileMinorVersion = showMinorVersion(fileMinor, fileExperimental)

    s"""TASTy signature has wrong version.
       | expected: {majorVersion: $MajorVersion, minorVersion: $minorVersion}
       | found   : {majorVersion: $fileMajor, minorVersion: $fileMinorVersion}
       |
       |""".stripMargin
  end signatureString

  private def unstableAddendum: String =
    """This TASTy file was produced by an unstable release.
      |To read this TASTy file, your tooling must be at the same version.""".stripMargin

  private def backIncompatAddendum: String =
    """This TASTy file was produced by an earlier release that is not supported anymore.
      |Please recompile this TASTy with a later version.""".stripMargin

  private def forwardIncompatAddendum: String =
    """This TASTy file was produced by a more recent, forwards incompatible release.
      |To read this TASTy file, please upgrade your tooling.""".stripMargin
end TastyHeaderUnpickler
