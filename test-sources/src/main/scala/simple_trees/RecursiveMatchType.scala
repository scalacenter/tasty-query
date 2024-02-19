package simple_trees

type RecursiveMatchType[A <: Tuple] <: Tuple = A match
  case hd *: tl => hd *: RecursiveMatchType[tl]
  case EmptyTuple => EmptyTuple

object RecursiveMatchType:
  inline def rec[A <: Tuple](a: A): RecursiveMatchType[A] =
    inline a match
      case b: (hd *: tl) => headOf(b) *: rec(tailOf(b))
      case _: EmptyTuple => EmptyTuple

  def headOf[H, T <: Tuple](t: H *: T): H = t.head
  def tailOf[H, T <: Tuple](t: H *: T): T = t.tail
end RecursiveMatchType

// must be in a separate TASTy file to trigger issue #401
object RecursiveMatchTypeTest:
  inline def rec[A <: Tuple](x: A): RecursiveMatchType[A] =
    RecursiveMatchType.rec(x)
end RecursiveMatchTypeTest
