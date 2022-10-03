/** Modified from dotty.tools.dotc.core.tasty.PositionUnpickler */

package tastyquery.reader

import scala.collection.mutable.HashMap

import dotty.tools.tasty.TastyBuffer.{Addr, NameRef}
import dotty.tools.tasty.TastyFormat.SOURCE
import dotty.tools.tasty.TastyReader

import tastyquery.Names.*
import tastyquery.Spans.*

/** Unpickler for tree positions */
class PositionUnpickler(reader: TastyReader, nameAtRef: TastyUnpickler.NameTable) {
  import reader.*

  private var myLineSizes: Array[Int] = _
  private var mySpans: HashMap[Addr, Span] = _
  private var mySourcePaths: HashMap[Addr, String] = _
  private var isDefined = false

  def ensureDefined(): Unit =
    if (!isDefined) {
      val lines = readNat()
      myLineSizes = new Array[Int](lines)
      var i = 0
      while i < lines do
        myLineSizes(i) += readNat()
        i += 1

      mySpans = HashMap[Addr, Span]()
      mySourcePaths = HashMap[Addr, String]()
      var curIndex = 0
      var curStart = 0
      var curEnd = 0
      while (!isAtEnd) {
        val header = readInt()
        if (header == SOURCE) {
          val path = nameAtRef.simple(readNameRef()).toString
          mySourcePaths(Addr(curIndex)) = path
        } else {
          val addrDelta = header >> 3
          val hasStart = (header & 4) != 0
          val hasEnd = (header & 2) != 0
          val hasPoint = (header & 1) != 0
          curIndex += addrDelta
          assert(curIndex >= 0)
          if (hasStart) curStart += readInt()
          if (hasEnd) curEnd += readInt()
          mySpans(Addr(curIndex)) =
            if (hasPoint) Span(curStart, curEnd, curStart + readInt())
            else Span(curStart, curEnd)
        }
      }
      isDefined = true
    }

  private def spans: HashMap[Addr, Span] = {
    ensureDefined()
    mySpans
  }

  private def sourcePaths: HashMap[Addr, String] = {
    ensureDefined()
    mySourcePaths
  }

  private def lineSizes: Array[Int] = {
    ensureDefined()
    myLineSizes
  }

  def spanAt(addr: Addr): Span = spans.getOrElse(addr, NoSpan)
  def sourcePathAt(addr: Addr): String = sourcePaths.getOrElse(addr, "")
}
