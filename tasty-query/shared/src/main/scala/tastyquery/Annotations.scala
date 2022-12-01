package tastyquery

import tastyquery.Trees.*

object Annotations:
  final class Annotation(val tree: TermTree):
    override def toString(): String = s"Annotation($tree)"
  end Annotation
end Annotations
