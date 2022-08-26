package simple_trees

class GenericClass[T](value: T):
  val field: T = value
  def getter: T = value
  def method(x: T): T = x
