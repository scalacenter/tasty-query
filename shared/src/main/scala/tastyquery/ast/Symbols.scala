package tastyquery.ast

import tastyquery.ast.Names.{Name, TypeName}

object Symbols {
  val NoSymbol = new Symbol(Names.EmptyTermName)
  // A placeholder for symbols that are not correctly created by tasty-query
  val DummySymbol = new Symbol(Names.EmptyTermName)

  class Symbol(val name: Name) {
    override def toString: String = s"symbol[$name]"
  }

  object Symbol {
    def unapply(s: Symbol): Option[Name] = Some(s.name)
  }

  class ClassSymbol(override val name: Name) extends Symbol(name)
}
