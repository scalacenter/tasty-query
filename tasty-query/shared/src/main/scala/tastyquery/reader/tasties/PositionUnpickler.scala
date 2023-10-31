/** Modified from dotty.tools.dotc.core.tasty.PositionUnpickler */

package tastyquery.reader.tasties

import scala.annotation.tailrec

import scala.collection.mutable

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.SourceFile
import tastyquery.SourcePosition
import tastyquery.Spans.*

import tastyquery.reader.ReaderContext
import tastyquery.reader.ReaderContext.rctx

import TastyFormat.SOURCE
import TastyReader.{Addr, NameRef}

/** Unpickler for tree positions */
private[reader] class PositionUnpickler(reader: TastyReader, nameAtRef: TastyUnpickler.NameTable)(using ReaderContext) {
  import reader.*

  private val mySpans = mutable.HashMap.empty[Addr, Span]
  private val mySourceFiles = mutable.HashMap.empty[Addr, SourceFile]
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

      /* Read the spans and SOURCE directives.
       *
       * SOURCE directives inherit their `curAddress` from the previous span entry.
       * They will apply to the tree at that address and all its subtree.
       */

      var noSourceSeenYet = true
      var curAddress = 0
      var curStart = 0
      var curEnd = 0

      while !isAtEnd do
        val header = readInt()
        if header == SOURCE then
          val path = nameAtRef.simple(readNameRef()).toString()
          val source = rctx.getSourceFile(path)
          mySourceFiles(Addr(curAddress)) = source

          // Attach the line sizes to the first source file we encounter
          if noSourceSeenYet then
            source.setLineSizes(myLineSizes)
            noSourceSeenYet = false
        else
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
          mySpans(Addr(curAddress)) = span
        end if
      end while

      isDefined = true
    }
  end ensureDefined

  def spanAt(addr: Addr): Span =
    ensureDefined()
    mySpans.getOrElse(addr, NoSpan)

  def hasSourceFileAt(addr: Addr): Boolean =
    ensureDefined()
    mySourceFiles.contains(addr)

  def sourceFileAt(addr: Addr, default: SourceFile): SourceFile =
    ensureDefined()
    mySourceFiles.getOrElse(addr, default)
}
