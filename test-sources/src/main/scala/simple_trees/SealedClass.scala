package simple_trees

sealed abstract class SealedClass

object SealedClass:
  case class ClassCase(x: Int) extends SealedClass
  case object ObjectCase extends SealedClass
end SealedClass
