package inheritance

object Overrides:
  class SuperMono:
    private def privateMethod(): Int = 1

    def foo(x: Int): String = x.toString()
    def foobaz[A](x: A, y: A): A = x

    def overloaded(x: Int): String = x.toString()
    def overloaded(x: java.lang.String): String = x

    def overloadedPoly[A](x: A): A = x
    def overloadedPoly[A, B](x: A, y: B): (A, B) = (x, y)

    override def toString(): String = "SuperMono"
  end SuperMono

  trait SuperMonoTrait:
    def bar(x: String, y: String): String = x.concat(y)

  class MidMono extends SuperMono with SuperMonoTrait

  class ChildMono extends MidMono:
    private def privateMethod(): Int = 2

    override def foo(x: Int): String = x.toString()
    override def foobaz[B](a: B, y: B): B = y
    override def bar(x: String, b: String): String = x

    override def overloaded(x: java.lang.String): String = x
    override def overloaded(x: Int): String = x.toString()

    override def overloadedPoly[B](a: B): B = a
    override def overloadedPoly[X, B](x: X, y: B): (X, B) = (x, y)

    override def toString: String = "ChildMono"
  end ChildMono

  class SuperPoly[A <: Product, B]:
    def foo(x: A): A = x
    def foo(x: B): B = x

  trait SecondSuperPoly[X <: Product]:
    def foo(x: X): X
    def foo(x: Int): Int

  trait ThirdSuper:
    def foo(x: String): String = x

  class ChildPoly[X <: Product] extends SuperPoly[X, Int] with SecondSuperPoly[X] with ThirdSuper:
    override def foo(x: X): X = x
    override def foo(x: Int): Int = x
end Overrides
