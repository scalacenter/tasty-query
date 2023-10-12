package simple_trees

class Tuples:
  def takeTuple(t: Tuple): Unit = ()

  def takeNonEmptyTuple(t: NonEmptyTuple): Unit = ()

  def takeStarColon(t: *:[Any, Tuple]): Unit = ()

  def takeEmptyTuple(t: EmptyTuple): Unit = ()

  def takeConcreteGenTuple(t: Int *: String *: EmptyTuple): Unit = ()

  def takeConcreteGenTupleThroughMatch(t: Tuple.Map[(Int, String), Option]): Unit = ()

  def calls(): Unit =
    takeTuple((1, 2))
    takeNonEmptyTuple((1, 2))
    takeStarColon((1, 2))
    takeEmptyTuple(EmptyTuple)
    takeConcreteGenTuple((1, "foo"))
    takeConcreteGenTupleThroughMatch((None, Some("foo")))
  end calls
end Tuples
