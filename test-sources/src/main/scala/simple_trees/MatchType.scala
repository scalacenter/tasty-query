package simple_trees

class MatchType {
  type MT[X] = X match {
    case Int => String
  }

  type MTWithBound[X] <: Product = X match {
    case Int => Some[Int]
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

  // For SignatureSuite
  def unboundUnreducibleSig[X](x: X): MT[X] = ???
  def unboundReducibleSig[X <: Int](x: Int): MT[X] = ???
  def boundUnreducibleSig[X](x: X): MTWithBound[X] = ???
  def boundReducibleSig[X <: Int](x: X): MTWithBound[X] = ???
  def arrayOfUnboundUnreducibleSig[X](x: X): Array[MT[X]] = ???
  def arrayOfUnboundReducibleSig[X <: Int](x: Int): Array[MT[X]] = ???
  def arrayOfBoundUnreducibleSig[X](x: X): Array[MTWithBound[X]] = ???
  def arrayOfBoundReducibleSig[X <: Int](x: X): Array[MTWithBound[X]] = ???

  val v = castMatchResult(5)
  val x = castMatchResultWithBind(List(5))
}
