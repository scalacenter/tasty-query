package simple_trees

class ForExpressions:
  val listOfTups = List((1, "foo"))

  def test1(): Unit =
    for (i, _) <- listOfTups do
      println(i)
  end test1
end ForExpressions
