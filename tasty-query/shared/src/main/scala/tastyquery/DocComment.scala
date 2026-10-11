package tastyquery

import tastyquery.Spans.Span

/** A documentation comment attached to a definition.
  *
  * @param raw
  *   the comment verbatim, including its `/**` and `*/` delimiters
  * @param span
  *   the span of the comment in the source file of the documented symbol
  */
final class DocComment private[tastyquery] (val raw: String, private val span: Span):
  /** The offset of the start of this comment. */
  def startOffset: Int = span.start

  /** The offset of the end of this comment. */
  def endOffset: Int = span.end

  override def toString(): String = s"DocComment($raw, $span)"
end DocComment
