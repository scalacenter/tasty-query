package scala2compat

class BoxedCons(val boxed: scala.collection.immutable.::[javadefined.JavaDefined]) {
  def foo = boxed.canEqual(scala.collection.immutable.Nil)
}
