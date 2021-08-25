package tastyquery

import dotty.tools.tasty.TastyBuffer.Addr
import dotty.tools.tasty.TastyFormat.NameTags
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Types.TypeLambda

import scala.collection.mutable
import scala.collection.mutable.HashMap

object Contexts {

  /** The current context */
  inline def ctx(using ctx: Context): Context = ctx

  def empty: Context = {
    val defn = new Definitions()
    new Context(defn.RootPackage, defn)
  }

  class Context private[Contexts] (
    val owner: Symbol,
    val defn: Definitions,
    val localSymbols: mutable.HashMap[Addr, Symbol] = new mutable.HashMap[Addr, Symbol]()
  ) {
    var enclosingLambdas: Map[Addr, TypeLambda] = Map.empty

    def withEnclosingLambda(addr: Addr, tl: TypeLambda): Context = {
      val copy = new Context(owner, defn, localSymbols)
      copy.enclosingLambdas = enclosingLambdas.updated(addr, tl)
      copy
    }

    def withOwner(newOwner: Symbol): Context =
      if (newOwner == owner) this
      else new Context(newOwner, defn, localSymbols)

    def hasSymbolAt(addr: Addr): Boolean = localSymbols.contains(addr)

    private def registerSym(addr: Addr, sym: Symbol, addToDecls: Boolean): Unit = {
      localSymbols(addr) = sym
      if (addToDecls && owner.isInstanceOf[DeclaringSymbol])
        owner.asInstanceOf[DeclaringSymbol].addDecl(sym)
    }

    /**
     * Creates a new symbol at @addr with @name. The symbol is added to the owner's declarations if both
     * 1) @addToDecls is true.
     *    Example: true for valdef and defdef, false for parameters and type parameters
     * 2) the owner is a declaring symbol.
     *    Example: a method is added to the declarations of its class, but a nested method is not added
     *    to declarations of its owner method.
     */
    def createSymbolIfNew[T <: Symbol](
      addr: Addr,
      name: Name,
      factory: SymbolFactory[T],
      addToDecls: Boolean = false
    ): T = {
      if (!hasSymbolAt(addr)) {
        registerSym(addr, factory.createSymbol(name, owner), addToDecls)
      }
      localSymbols(addr).asInstanceOf[T]
    }

    def createPackageSymbolIfNew(name: TermName): PackageClassSymbol = {
      def create(): PackageClassSymbol = {
        val trueOwner = if (owner == defn.EmptyPackage) defn.RootPackage else owner
        val sym       = PackageClassSymbolFactory.createSymbol(name, trueOwner)
        sym
      }

      defn.RootPackage.findPackageSymbol(name) match {
        case Some(pkg) => pkg
        case None =>
          name match {
            case _: SimpleName => create()
            case QualifiedName(NameTags.QUALIFIED, prefix, _) =>
              if (prefix == owner.name) {
                create()
              } else {
                // create intermediate packages
                val newOwner = createPackageSymbolIfNew(prefix)
                withOwner(newOwner).createPackageSymbolIfNew(name)
              }
            case _ =>
              throw IllegalArgumentException(s"Unexpected package name: $name")
          }
      }
    }

    def getPackageSymbol(name: TermName): PackageClassSymbol = defn.RootPackage.findPackageSymbol(name).get

    def getSymbol(addr: Addr): Symbol =
      localSymbols(addr)
    def getSymbol[T <: Symbol](addr: Addr, symbolFactory: SymbolFactory[T]): T =
      symbolFactory.castSymbol(localSymbols(addr))
  }
}
