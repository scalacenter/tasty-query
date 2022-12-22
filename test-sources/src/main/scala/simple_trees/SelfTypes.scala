package simple_trees

object SelfTypes:
  trait Foo[T]:
    self: Bar[T, Int] =>

    def throughSelf: Pair[T, Int] = self.bar()
    def throughThis: MyPair = this.bar()
    def bare: Pair[T, Int] = bar()
  end Foo

  trait Bar[A, B]:
    def bar(): Pair[A, B]

    type MyPair = Pair[A, B]
  end Bar

  class FooBar extends Foo[String] with Bar[String, Int]:
    def bar(): Pair[String, Int] = Pair("foo", 4)
  end FooBar

  final class Pair[+A, +B](val a: A, val B: B)
end SelfTypes
