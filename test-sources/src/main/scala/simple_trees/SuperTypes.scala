package simple_trees

object SuperTypes:
  class Foo:
    final val foo: "Foo.foo" = "Foo.foo"
  end Foo

  class Bar extends Foo:
    def bar: Bar.super.foo.type = "" match
      case A(x) => x

    object A:
      def unapply(a: Any) =
        Some[Bar.super.foo.type](Bar.this.foo)
    end A
  end Bar

  class Baz extends Foo:
    object A:
      def unapply(a: Any) =
        Some[Baz.super[Foo].foo.type](Baz.this.foo)
    end A

    def baz: Baz.super[Foo].foo.type = "" match
      case A(x) => x
  end Baz
end SuperTypes
