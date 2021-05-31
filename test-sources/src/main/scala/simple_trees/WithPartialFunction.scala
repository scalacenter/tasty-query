package simple_trees

class WithPartialFunction {
  val partial: PartialFunction[Int, Int] = { case 0 =>
    1
  }
}
