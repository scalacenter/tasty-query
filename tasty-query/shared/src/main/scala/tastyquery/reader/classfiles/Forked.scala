package tastyquery.reader.classfiles

private[classfiles] trait Forked[Child] {
  def use[T](op: Child ?=> T): T
}
