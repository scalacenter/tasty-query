package simple_trees

class RefinedTypeTree {
  type Refined = TypeMember { type AbstractType = Int }

  // Refining an existing term member

  abstract class A {
    def m(): Any
  }

  val a: B { def b: A } = new B { def b: A = ??? }

  def foo(a: A { def m(): Int }): Int = a.m()

  def bar(x: Int): A { def m(): Int } = new A { def m(): Int = x }

  // Adding an otherwise non-existing term member

  abstract class B

  def foo2(a: B { def m(): Int }): Int = 5

  def bar2(x: Int): B { def m(): Int } = new B { def m(): Int = x }

  def foobar2(a: B { def m(): Int}): B { def m(): Int } = a

  // When we need the ThisType of the refinement itself

  trait C {
    class C1
  }

  def innerRef(c: C { def c1: C1 }): Int = ???

  val innerRefVal: C { def c1: C1 } = new C { def c1: C1 = new C1}

  // With an additional 'with'

  trait AndTypeA
  trait AndTypeB extends AndTypeA

  def andType(): AndTypeA with AndTypeB { def foo: String } =
    new AndTypeA with AndTypeB { def foo: String = toString }
}
