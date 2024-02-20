package simple_trees

final class ValueClass(val it: List[?]) extends AnyVal {
  def myLength: Int = it.size
}
