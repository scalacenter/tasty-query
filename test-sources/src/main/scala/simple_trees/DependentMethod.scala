package simple_trees

class DependentMethod {

  def id(x: Any): x.type = x

  val test = id("hello")

}
