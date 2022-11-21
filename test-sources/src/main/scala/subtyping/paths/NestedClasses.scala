package subtyping.paths

object NestedClasses:
  class Parent

  class Outer(x: Int):
    class Inner(y: Int) extends Parent

  val outer = new Outer(5)
  val inner = new outer.Inner(6)
end NestedClasses
