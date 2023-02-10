package simple_trees

class UnionType {
  def argWithOrType(x: Int | String) = x

  def classesOrType(x: List[Int] | Vector[String]): Seq[Int | String] = x

  def arrayOfUnion(x: Array[AnyRef | Null]): Array[AnyRef | Null] = x
}
