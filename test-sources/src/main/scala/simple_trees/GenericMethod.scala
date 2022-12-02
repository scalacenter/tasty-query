package simple_trees

import scala.annotation.targetName

class GenericMethod {
  def usesTypeParam[T](): Option[T] = None
  def usesTermParam(i: Int): Option[Int] = None

  def identity[T](x: T): T = x

  @targetName("otherName")
  def otherIdentity[T](x: T): T = x
}
