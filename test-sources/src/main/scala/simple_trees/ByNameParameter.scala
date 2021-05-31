package simple_trees

class ByNameParameter {
  def withByName(x: => Int): Int = x
}
