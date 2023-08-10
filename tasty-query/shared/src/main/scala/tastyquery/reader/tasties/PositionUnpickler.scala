/** Modified from dotty.tools.dotc.core.tasty.PositionUnpickler */

package tastyquery.reader.tasties

import scala.collection.mutable
import scala.compiletime.uninitialized

import dotty.tools.tasty.TastyBuffer.{Addr, NameRef}
import dotty.tools.tasty.TastyFormat.SOURCE
import dotty.tools.tasty.TastyReader

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.SourceFile
import tastyquery.SourcePosition
import tastyquery.Spans.*

/** Unpickler for tree positions */
private[reader] class PositionUnpickler(reader: TastyReader, nameAtRef: TastyUnpickler.NameTable)(using Context) {
  import reader.*

  private val mySourcePositions = mutable.HashMap.empty[Addr, SourcePosition]
  private var isDefined = false

  def ensureDefined(): Unit =
    if (!isDefined) {
      // Read the line sizes array; we will attach it to the first SOURCE directive we encounter

      val lines = readNat()
      val myLineSizes = new Array[Int](lines)
      var i = 0
      while i < lines do
        myLineSizes(i) += readNat()
        i += 1

      /* Read the source positions
       * There are spans and SOURCE directives. A source directive applies to
       * the span *just before it* and the following. This is a peculiarity due
       * to how dotc maintains the addresses of spans and sources. For us, it
       * makes the unpickling algorithm a bit messy.
       */

      var noSourceSeenYet = true
      var curSource = SourceFile.NoSource
      var curAddress = 0
      var curStart = 0
      var curEnd = 0

      var eof = false
      var header = readInt()
      while !eof do
        val addressDelta = header >> 3
        val hasStart = (header & 4) != 0
        val hasEnd = (header & 2) != 0
        val hasPoint = (header & 1) != 0

        curAddress += addressDelta
        assert(curAddress >= 0)
        if hasStart then curStart += readInt()
        if hasEnd then curEnd += readInt()
        val span =
          if hasPoint then Span(curStart, curEnd, curStart + readInt())
          else Span(curStart, curEnd)

        if isAtEnd then eof = true
        else
          header = readInt()
          if header == SOURCE then
            val path = nameAtRef.simple(readNameRef()).toString()
            curSource = ctx.getSourceFile(path)
            if noSourceSeenYet then
              curSource.setLineSizes(myLineSizes)
              noSourceSeenYet = false

            if isAtEnd then eof = true
            else header = readInt()
        end if

        mySourcePositions(Addr(curAddress)) = new SourcePosition(curSource, span)
      end while

      isDefined = true
    }
  end ensureDefined

  def sourcePositionAt(addr: Addr): SourcePosition =
    ensureDefined()
    mySourcePositions.getOrElse(addr, SourcePosition.NoPosition)
}
