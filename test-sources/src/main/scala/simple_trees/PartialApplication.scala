package simple_trees

class PartialApplication {
  def withManyParams(first: Int)(second: Int): Int = first

  def partiallyApplied = withManyParams(0)
}
