package simple_trees

object SuperDoubleDiamond:
  // Lin = A, AnyRef
  trait A:
    def foo = 2

  // Lin = B, AnyRef
  trait B:
    def foo = 3

  // Lin = AA, A, AnyRef
  trait AA extends A:
    def foo: Int

  // Lin = BB, B, AnyRef
  trait BB extends B:
    override def foo = super.foo

  // Lin = AB, B, A, AnyRef
  trait AB extends A, B:
    override def foo = super.foo

  // Lin = AAABBB, BB, AB, B, AA, A, AnyRef
  class AAABBB extends AA, AB, BB:
    override def foo = super.foo

  // Lin = AABBAB, AB, BB, B, AA, A, AnyRef
  class AABBAB extends AA, BB, AB
end SuperDoubleDiamond
