package simple_trees

class MatchType {
  type MT[X] = X match {
    case Int => String
  }

  type MTWithBound[X] <: Nothing = X match {
    case Int => Nothing
  }

  type MTWithWildcard[X] = X match {
    case _ => Int
  }

  type MTWithBind[X] = X match {
    case List[t] => t
  }

  def castMatchResult[X](x: X): MT[X] = x match
    case i: Int => i.toString

  def castMatchResultWithBind[X](x: X): MTWithBind[X] = x match
    case is: List[t] => is.head

  val v = castMatchResult(5)
  val x = castMatchResultWithBind(List(5))
}
