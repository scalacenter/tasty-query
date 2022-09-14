package simple_trees

trait HigherKinded[A[_]] {
  def m[T](x: A[T]): A[T]
}
