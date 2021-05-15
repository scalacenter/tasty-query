package simple_trees

class Base {
  def f: Unit = ()
}

class Super extends Base {
  super.f
  super[Base].f
}
