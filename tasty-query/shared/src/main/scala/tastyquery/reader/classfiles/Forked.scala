package tastyquery.reader.classfiles

trait Forked[Child] {
  def use[T](op: Child ?=> T): T
}
