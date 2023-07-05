package simple_trees

class UsingGiven {
  given Int = 0

  def useNormal(x: Int): Int = x

  def useGiven(using Int) = ()

  useGiven
  useGiven(using 0)

  def useImplicit(implicit x: Int): Int = x

  def refinementWithNormal: Any { def foo(x: Int): Int } = ???
  def refinementWithUsing: Any { def foo(using x: Int): Int } = ???
  def refinementWithImplicit: Any { def foo(implicit x: Int): Int } = ???
}
