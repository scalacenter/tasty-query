package simple_trees

class UnionType {
  def argWithOrType(x: Int | String) = x

  def classesOrType(x: List[Int] | Vector[String]): Seq[Int | String] = x
}
