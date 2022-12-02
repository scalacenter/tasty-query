package simple_trees

import scala.annotation.targetName

class OverloadedApply {

  object Foo {
    object Bar
  }

  class Box[T](val x: T)

  class Num

  def foo(a: Int): Unit = ()
  def foo(a: Box[Num]): Unit = ()
  def foo(a: Foo.Bar.type): Unit = ()
  def foo(a: Array[Foo.type]): Unit = ()
  def foo(a: => Num): Unit = ()
  def foo: String = "foo"

  @targetName("bar") def foo(a: Box[Int]): Unit = ()

  def callA = foo(1)
  def callB = foo(Box(new Num))
  def callC = foo(Foo.Bar)
  def callD = foo(Array(Foo))
  def callE = foo(Num())
  def callF = foo
  def callG = foo(Box(3))

}
