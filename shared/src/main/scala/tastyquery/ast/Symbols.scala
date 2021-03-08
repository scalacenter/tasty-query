package tastyquery.ast

import tastyquery.ast.Names.{Name, TypeName}

abstract class Designator

object Symbols {
  val NoSymbol = new Symbol(Names.EmptyTermName)
  // A placeholder for symbols that are not correctly created by tasty-query
  val DummySymbol = new Symbol(Names.EmptyTermName)

  class Symbol(val name: Name) extends Designator {
    override def toString: String = s"symbol[$name]"
  }
}
