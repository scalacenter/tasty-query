package simple_trees

class NamedArgument {
  def withNamed(first: Int, second: Int): Unit = ()

  withNamed(0, second = 1)
}
