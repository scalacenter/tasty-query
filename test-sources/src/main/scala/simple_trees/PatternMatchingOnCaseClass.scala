package simple_trees

abstract class AbstractForCaseClasses

case class FirstCase(x: Int) extends AbstractForCaseClasses

case class SecondCase(y: Int) extends AbstractForCaseClasses

class PatternMatchingOnCaseClass {
  def caseMatching(c: AbstractForCaseClasses): Int =
    c match {
      case FirstCase(x)  => x
      case SecondCase(y) => y
      case _             => 0
    }
}
