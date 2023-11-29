package simple_trees

object PathDependentOpaque:
  trait Foo[T]:
    opaque type Type <: T = T

    protected def make(t: T): Type = t
  end Foo

  class Bar extends Foo[String]:
    def bar(x: Type): Unit = ()

    def get(): Type = make("hello")
  end Bar

  def test(): Unit =
    val b = new Bar()
    b.bar(b.get())
end PathDependentOpaque
