package inheritance

object SameTasty:

  abstract class Parent:
    def foo: Int = 23

  /** Defined in a same tasty file as Parent */
  class Sub extends Parent
