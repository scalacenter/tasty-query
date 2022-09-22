package inheritance

object SameTasty:

  abstract class Parent:
    def foo: Int = 23

  /** Defined in a same tasty file as Parent */
  class Sub extends Parent

  trait Mixin:
    def bar: Int = 29

  trait SubMixin extends Mixin

  class WithMixin extends AnyRef with SubMixin

  class SubWithMixin extends WithMixin
