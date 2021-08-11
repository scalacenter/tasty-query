package simple_trees

class UsingGiven {
  given Int = 0

  def useGiven(using Int) = ()

  useGiven
  useGiven(using 0)
}
