package tastyquery

import dotty.tools.tasty.TastyBuffer.Addr
import tastyquery.ast.Names.Name
import tastyquery.ast.Symbols.{NoSymbol, Symbol}

import scala.collection.mutable
import scala.collection.mutable.HashMap

object Contexts {

  /** The current context */
  inline def ctx(using ctx: Context): Context = ctx

  def empty: Context = new Context()

  class Context(localSymbols: HashMap[Addr, Symbol] = new mutable.HashMap[Addr, Symbol]()) {
    def hasSymbolAt(addr: Addr): Boolean = localSymbols.contains(addr)

    def registerSym(addr: Addr, sym: Symbol): Unit =
      localSymbols(addr) = sym

    def createSymbol(addr: Addr, name: Name): Unit =
      registerSym(addr, new Symbol(name))

    def createClassSymbol(addr: Addr, name: Name): Unit =
      registerSym(addr, new Symbol(name))
  }
}
