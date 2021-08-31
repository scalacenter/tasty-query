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
    val owner: DeclaringSymbol,
    val defn: Definitions,
    val localSymbols: HashMap[Addr, Symbol] = new mutable.HashMap[Addr, Symbol]()
  ) {
    var enclosingLambdas: Map[Addr, TypeLambda] = Map.empty

    def withEnclosingLambda(addr: Addr, tl: TypeLambda): Context = {
      val copy = new Context(owner, defn, localSymbols)
      copy.enclosingLambdas = enclosingLambdas.updated(addr, tl)
      copy
    }

    def withOwner(newOwner: DeclaringSymbol): Context =
      if (newOwner == owner) this
      else new Context(newOwner, defn, localSymbols)

    def hasSymbolAt(addr: Addr): Boolean = localSymbols.contains(addr)

    def registerSym(addr: Addr, sym: Symbol): Unit = {
      localSymbols(addr) = sym
      owner.addDecl(sym)
    }

    def createSymbolIfNew(addr: Addr, name: Name): Symbol = {
      if (!hasSymbolAt(addr)) {
        registerSym(addr, new Symbol(name, owner))
      }
      localSymbols(addr)
    }

    def createClassSymbolIfNew(addr: Addr, name: Name): ClassSymbol = {
      if (!hasSymbolAt(addr)) {
        registerSym(addr, new ClassSymbol(name, owner))
      }
      localSymbols(addr).asInstanceOf[ClassSymbol]
    }

    def createMethodSymbolIfNew(addr: Addr, name: TermName): MethodSymbol = {
      if (!hasSymbolAt(addr)) {
        registerSym(addr, new MethodSymbol(name, owner))
      }
      localSymbols(addr).asInstanceOf[MethodSymbol]
    }

    def createPackageSymbolIfNew(name: TermName): PackageClassSymbol = {
      def create(): PackageClassSymbol = {
        val trueOwner = if (owner == defn.EmptyPackage) defn.RootPackage else owner
        val sym = new PackageClassSymbol(name, trueOwner)
        sym
      }

      getPackageSymbol(name) match {
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

    def getPackageSymbol(name: TermName): Option[PackageClassSymbol] = defn.RootPackage.findPackageSymbol(name)

    def getSymbol(addr: Addr): Symbol = localSymbols(addr)
  }
}
