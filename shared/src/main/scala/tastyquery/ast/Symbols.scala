package tastyquery.ast

import tastyquery.ast.Names.Name

object Symbols {
  val NoSymbol = new Symbol(Names.EmptyTermName)

  class Symbol(val name: Name) {
    override def toString: String = s"symbol[$name]"
  }

  class ClassSymbol(override val name: Name) extends Symbol(name)
}
