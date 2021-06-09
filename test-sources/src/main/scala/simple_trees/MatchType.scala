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
}
