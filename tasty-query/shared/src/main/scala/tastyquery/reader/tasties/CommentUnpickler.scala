package tastyquery.reader.tasties

import tastyquery.DocComment
import tastyquery.Spans.*

import tastyquery.reader.UTF8Utils

import TastyReader.Addr

private[reader] class CommentUnpickler(reader: TastyReader) {
  import reader.*

  private val comments: Map[Addr, DocComment] =
    val builder = Map.newBuilder[Addr, DocComment]
    while !isAtEnd do
      val addr = readAddr()
      val length = readNat()
      val start = currentAddr
      goto(start + length)
      val span = spanFromCoord(readLongInt())
      builder += addr -> DocComment(UTF8Utils.decode(bytes, index(start), length), span)
    builder.result()

  def commentAt(addr: Addr): Option[DocComment] =
    comments.get(addr)
}
