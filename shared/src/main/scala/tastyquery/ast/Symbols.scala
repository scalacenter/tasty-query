package tastyquery.ast

import scala.collection.mutable
import tastyquery.ast.Names.*
import dotty.tools.tasty.TastyFormat.NameTags
import tastyquery.ast.Trees.{EmptyTree, Tree}

object Symbols {
  class SymbolLookupException(val name: Name, explanation: String = "")
      extends RuntimeException(
        SymbolLookupException.addExplanation(s"Could not find symbol for name ${name.toDebugString}", explanation)
      )

  object SymbolLookupException {
    def unapply(e: SymbolLookupException): Option[Name] = Some(e.name)

    def addExplanation(msg: String, explanation: String): String =
      if (explanation.isEmpty) msg else s"$msg: $explanation"
  }

  val NoSymbol = new RegularSymbol(Names.EmptyTermName, null)

  abstract class Symbol private[Symbols] (val name: Name, val owner: Symbol | Null) {
    protected var myTree: Tree = EmptyTree
    // overridden in package symbol
    def withTree(t: Tree): this.type = {
      myTree = t
      this
    }
    final def tree: Tree = myTree

    override def toString: String = s"symbol[$name]"
    def toDebugString = toString
  }

  object Symbol {
    def unapply(s: Symbol): Option[Name] = Some(s.name)
  }

  final class RegularSymbol(override val name: Name, override val owner: Symbol | Null) extends Symbol(name, owner)

  abstract class DeclaringSymbol(override val name: Name, override val owner: Symbol | Null)
      extends Symbol(name, owner) {
    /* A map from the name of a declaration directly inside this symbol to the corresponding symbol
     * The qualifiers on the name are not dropped. For instance, the package names are always fully qualified. */
    protected val myDeclarations: mutable.HashMap[Name, mutable.HashSet[Symbol]] =
      mutable.HashMap[Name, mutable.HashSet[Symbol]]()

    def addDecl(decl: Symbol): Unit = myDeclarations.getOrElseUpdate(decl.name, new mutable.HashSet) += decl
    def getDecl(name: Name): Option[Symbol] = name match {
      case overloaded: SignedName => resolveOverloaded(overloaded)
      case name =>
        myDeclarations.get(name).collect {
          case set if set.sizeIs == 1 => set.head
        }
    }
    def resolveOverloaded(name: SignedName): Option[Symbol] =
      getDecl(name.underlying) // TODO: look at signature to filter overloads

    def declarations: List[Symbol] = myDeclarations.values.toList.flatten

    override def toDebugString: String =
      s"${super.toString} with declarations [${myDeclarations.keys.map(_.toDebugString).mkString(", ")}]"
  }

  class ClassSymbol(override val name: Name, override val owner: Symbol | Null) extends DeclaringSymbol(name, owner) {
    private[tastyquery] var initialised: Boolean = false
  }

  // TODO: typename or term name?
  class PackageClassSymbol(override val name: Name, override val owner: PackageClassSymbol | Null)
      extends ClassSymbol(name, owner) {
    if (owner != null) {
      // A package symbol is always a declaration in its owner package
      owner.addDecl(this)
    } else {
      // Root package is the only symbol that is allowed to not have an owner
      assert(name == RootName)
    }
    def findPackageSymbol(packageName: TermName): Option[PackageClassSymbol] = packageName match {
      case _: SimpleName => getPackageDecl(packageName)
      case QualifiedName(NameTags.QUALIFIED, prefix, suffix) =>
        if (prefix == name)
          getPackageDecl(packageName)
        else
          // recurse
          findPackageSymbol(prefix).flatMap(_.findPackageSymbol(packageName))
      case _ => throw IllegalArgumentException(s"Unexpected package name: $name")
    }

    private def getPackageDecl(packageName: TermName): Option[PackageClassSymbol] =
      getDecl(packageName).map(_.asInstanceOf[PackageClassSymbol])

    override def withTree(t: Tree): PackageClassSymbol.this.type = throw new UnsupportedOperationException(
      s"Multiple trees correspond to one package, a single tree cannot be assigned"
    )
  }

  abstract class SymbolFactory[T <: Symbol] {
    def createSymbol(name: Name, owner: Symbol): T
    def castSymbol(symbol: Symbol): T
  }

  object RegularSymbolFactory extends SymbolFactory[RegularSymbol] {
    override def createSymbol(name: Name, owner: Symbol): RegularSymbol = new RegularSymbol(name, owner)

    override def castSymbol(symbol: Symbol): RegularSymbol = symbol.asInstanceOf[RegularSymbol]
  }

  object ClassSymbolFactory extends SymbolFactory[ClassSymbol] {
    override def createSymbol(name: Name, owner: Symbol): ClassSymbol = new ClassSymbol(name, owner)

    override def castSymbol(symbol: Symbol): ClassSymbol = symbol.asInstanceOf[ClassSymbol]
  }

  object PackageClassSymbolFactory extends SymbolFactory[PackageClassSymbol] {
    override def createSymbol(name: Name, owner: Symbol): PackageClassSymbol =
      new PackageClassSymbol(name, owner.asInstanceOf[PackageClassSymbol])

    override def castSymbol(symbol: Symbol): PackageClassSymbol = symbol.asInstanceOf[PackageClassSymbol]
  }
}
