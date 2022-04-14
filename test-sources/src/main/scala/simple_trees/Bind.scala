package simple_trees

class Bind {
  def f(x: Any): Unit = x match {
    case t @ y: Int =>
    case s: String =>
    case k @ Some(_) =>
    case _ =>
  }
}