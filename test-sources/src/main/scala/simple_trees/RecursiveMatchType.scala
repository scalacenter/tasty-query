package simple_trees

type RecursiveMatchType[A <: Tuple] <: Tuple = A match
  case hd *: tl => hd *: RecursiveMatchType[tl]
  case EmptyTuple => EmptyTuple

object RecursiveMatchType:
  inline def rec[A <: Tuple](a: A): RecursiveMatchType[A] =
    inline a match
      case b: (hd *: tl) => b.head *: rec(b.tail)
      case _: EmptyTuple => EmptyTuple
end RecursiveMatchType

// must be in a separate TASTy file to trigger issue #401
object RecursiveMatchTypeTest:
  inline def rec[A <: Tuple](x: A): RecursiveMatchType[A] =
    RecursiveMatchType.rec(x)
end RecursiveMatchTypeTest
