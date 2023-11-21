package simple_trees

class DefaultParams:
  def foo(x: Int, y: Int = 1, z: String = "hello"): String = s"$x $y $z"

  def foo(x: Int, y: String): String = s"$x $y"
end DefaultParams
