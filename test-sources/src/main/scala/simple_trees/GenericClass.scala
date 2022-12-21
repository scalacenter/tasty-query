package simple_trees

class GenericClass[T](value: T):
  def this() = this(???)

  val field: T = value
  def getter: T = value
  def method(x: T): T = x
end GenericClass

object GenericClass:
  def new1(): GenericClass[Int] = new GenericClass[Int](1)
  def new2(): GenericClass[Int] = new GenericClass(1)
  def new3(): GenericClass[Int] = new GenericClass
end GenericClass
