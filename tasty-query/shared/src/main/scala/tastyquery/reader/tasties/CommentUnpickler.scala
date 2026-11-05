/** Modified from dotty.tools.dotc.core.tasty.CommentUnpickler */

package tastyquery.reader.tasties

import scala.collection.mutable

import tastyquery.reader.UTF8Utils

import TastyReader.Addr

/** Unpickler for documentation comments of symbols */
private[reader] class CommentUnpickler(reader: TastyReader) {
  import reader.*

  private val myComments = mutable.HashMap.empty[Addr, String]
  private var isDefined = false

  private def readUtf8(): String =
    val length = readNat()
    val start = currentAddr
    goto(start + length)
    UTF8Utils.decode(bytes, index(start), length)
  end readUtf8

  def ensureDefined(): Unit =
    if (!isDefined) {
      /* Read the comments and their spans.
       *
       * Each entry is the address of the documented definition, the raw
       * comment as written in the source code, and the span of the comment,
       * which is not needed to answer `commentAt`.
       */
      while (!isAtEnd) {
        val addr = readAddr()
        val comment = readUtf8()
        readLongInt() // span coordinates
        myComments(addr) = comment
      }
      isDefined = true
    }
  end ensureDefined

  def commentAt(addr: Addr): Option[String] =
    ensureDefined()
    myComments.get(addr)

  /** Iterate over all loaded comments and apply the given function. */
  private[tasties] def allComments: Iterator[(Addr, String)] =
    ensureDefined()
    myComments.iterator
}
