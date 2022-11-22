package inheritance

object SameTasty:

  abstract class Parent:
    type FooType
    def foo: FooType
    def getFoo(): FooType = foo
    //def maybePrivateMember: Int = 5

  class Child extends Parent:
    type FooType = Int
    def foo: FooType = 23
    private def maybePrivateMember: Int = 6

  class Sub extends Child:
    def foo3: FooType = foo
    def maybePrivateMember: Int = 7

  trait Mixin:
    type BarType
    def bar: BarType
    def getBar(): BarType = bar

  trait SubMixin extends Mixin:
    type BarType = Int
    def bar: BarType = 29

  class WithMixin extends AnyRef with SubMixin

  class SubWithMixin extends WithMixin:
    def bar3: BarType = bar

  def tests(): Unit =
    val sub = new Sub
    val foo1 = sub.foo
    val foo2 = sub.getFoo()
    val foo3 = sub.foo3

    val subWithMixin = new SubWithMixin
    val bar1 = subWithMixin.bar
    val bar2 = subWithMixin.getBar()
    val bar3 = subWithMixin.bar3
  end tests

end SameTasty
