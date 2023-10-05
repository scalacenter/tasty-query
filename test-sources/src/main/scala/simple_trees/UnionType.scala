package simple_trees

class UnionType {
  def argWithOrType(x: Int | String) = x

  def classesOrType(x: List[Int] | Vector[String]): Seq[Int | String] = x

  def arrayOfUnion(x: Array[AnyRef | Null]): Array[AnyRef | Null] = x

  def unitOrNull(x: Unit | Null): Unit | Null = x

  def intOrNull(x: Int | Null): Int | Null = x

  def optionOrNull(x: Option[Int] | Null): Option[Int] | Null = x

  def optionOrUnit(x: Option[Int] | Unit): Option[Int] | Unit = x

  def calls(): Unit =
    argWithOrType(5)
    classesOrType(Nil)
    arrayOfUnion(Array())
    unitOrNull(())
    intOrNull(5)
    optionOrNull(None)
    optionOrUnit(())
}
