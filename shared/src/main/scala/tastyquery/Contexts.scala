package tastyquery

import dotty.tools.tasty.TastyBuffer.Addr
import tastyquery.ast.Names.Name
import tastyquery.ast.Symbols.{NoSymbol, Symbol}
import tastyquery.ast.Types.TypeLambda

import scala.collection.mutable
import scala.collection.mutable.HashMap

object Contexts {

  /** The current context */
  inline def ctx(using ctx: Context): Context = ctx

  def empty: Context = new Context()

  class Context(val localSymbols: HashMap[Addr, Symbol] = new mutable.HashMap[Addr, Symbol]()) {
    var enclosingLambdas: Map[Addr, TypeLambda] = Map.empty

    def withEnclosingLambda(addr: Addr, tl: TypeLambda): Context = {
      val copy = new Context(localSymbols)
      copy.enclosingLambdas = enclosingLambdas.updated(addr, tl)
      copy
    }

    def hasSymbolAt(addr: Addr): Boolean = localSymbols.contains(addr)

    def registerSym(addr: Addr, sym: Symbol): Unit =
      localSymbols(addr) = sym

    def createSymbolIfNew(addr: Addr, name: Name): Unit =
      if (!hasSymbolAt(addr)) {
        registerSym(addr, new Symbol(name))
      }

    def createClassSymbolIfNew(addr: Addr, name: Name): Unit =
      if (!hasSymbolAt(addr)) {
        registerSym(addr, new Symbol(name))
      }
  }
}
