package simple_trees

trait HigherKinded[A[_]] {
  def m[T](x: A[T]): A[T]

  def f[B[_], T](x: B[T]): B[T]
}
