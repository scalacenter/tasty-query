package simple_trees

object UnionTypeJoin:
  trait C[+T]
  trait D
  trait E
  class A extends C[A] with D
  class B extends C[B] with D with E
end UnionTypeJoin
