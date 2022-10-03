package tastyquery.util

trait Forked[Child] {
  def use[T](op: Child ?=> T): T
}
