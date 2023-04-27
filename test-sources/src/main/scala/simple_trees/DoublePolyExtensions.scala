package simple_trees

class DoublePolyExtensions:
  extension [A] (list: List[A])
    // name must end with : to trigger a double-type-param list
    def +++: [B >: A](x: B): List[B] = x :: list

  def f(xs: List[Int]): List[Any] =
    xs +++: "hello"
end DoublePolyExtensions
