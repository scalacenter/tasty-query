package tastyquery.ast

import tastyquery.ast.Names.Name

abstract class Designator

object Symbols {
  val NoSymbol = new Symbol(Names.EmptyTermName)

  class Symbol(val name: Name) extends Designator {
    override def toString: String = s"symbol[$name]"
  }
}
