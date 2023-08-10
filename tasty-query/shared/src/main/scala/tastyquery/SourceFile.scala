package tastyquery

import java.util.Arrays

final class SourceFile private[tastyquery] (_path: String):
  /** The full, though usually relative, path of the file, as stored in TASTy. */
  def path: String = _path

  /** The last `/`-separated component of the `path`. */
  def name: String = path.substring(path.lastIndexOf('/') + 1).nn

  override def toString(): String = path

  private var lineStartOffsets: Array[Int] | Null = null

  /** Tests whether this source file gives line/column information. */
  def hasLineColumnInformation: Boolean = lineStartOffsets != null

  private[tastyquery] def setLineSizes(lineSizes: Array[Int]): Unit =
    // Several .tasty files can come from the same source file, so we might call this several times.
    if lineStartOffsets == null then
      // Expand line sizes into line offsets
      val startOffsets = new Array[Int](lineSizes.length + 1)
      startOffsets(0) = 0
      for i <- 1 until startOffsets.length do
        startOffsets(i) = startOffsets(i - 1) + lineSizes(i - 1) + 1 // + 1 for the '\n'
      lineStartOffsets = startOffsets
  end setLineSizes

  private def ensureLineStartOffsets(): Array[Int] =
    val startOffsets = lineStartOffsets
    if startOffsets != null then startOffsets
    else throw UnsupportedOperationException(s"Source file $path does not have line/column information")

  private def lineToOffset(line: Int): Int =
    ensureLineStartOffsets()(line)

  private[tastyquery] def offsetToLine(offset: Int): Int =
    val startOffsets = ensureLineStartOffsets()
    val p = Arrays.binarySearch(startOffsets, offset)
    if p >= 0 then p
    else (-p - 1) - 1 // (-p - 1) is the insertion point, from which we still need to subtract 1 to get the line
  end offsetToLine

  private[tastyquery] def offsetToColumn(offset: Int): Int =
    offset - lineToOffset(offsetToLine(offset))
end SourceFile

object SourceFile:
  val NoSource: SourceFile =
    val noSource = new SourceFile("")
    noSource.setLineSizes(new Array(0)) // prevent anyone from attempting to fill in line sizes for NoSource
    noSource
  end NoSource
end SourceFile
