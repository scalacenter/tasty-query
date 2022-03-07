package tastyquery.ast

import scala.collection.mutable
import tastyquery.ast.Names.{Name, TermName, SignedName, SimpleName, QualifiedName, nme}
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

  val NoSymbol = new RegularSymbol(nme.EmptyTermName, null)

  abstract class Symbol private[Symbols] (val name: Name, rawowner: Symbol | Null) {
    protected var myTree: Tree = EmptyTree
    // overridden in package symbol
    def withTree(t: Tree): this.type = {
      myTree = t
      this
    }
    final def tree: Tree = myTree

    final def outer: Symbol = rawowner match {
      case owner: Symbol => owner
      case null          => assert(false, s"cannot access outer, $this was not declared within any scope")
    }

    final def enclosingDecl: DeclaringSymbol = rawowner match {
      case owner: DeclaringSymbol => owner
      case _: Symbol | null       => assert(false, s"cannot access owner, $this is a local symbol or has no owner")
    }

    final def isClass: Boolean = this.isInstanceOf[ClassSymbol]

    override def toString: String = {
      val kind = this match
        case _: PackageClassSymbol => "package "
        case _: ClassSymbol        => "class "
        case _                     => ""
      s"symbol[$kind$name]"
    }
    def toDebugString = toString
  }

  object Symbol {
    def unapply(s: Symbol): Option[Name] = Some(s.name)
  }

  final class RegularSymbol(override val name: Name, rawowner: Symbol | Null) extends Symbol(name, rawowner)

  abstract class DeclaringSymbol(override val name: Name, rawowner: Symbol | Null) extends Symbol(name, rawowner) {
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

  class ClassSymbol(override val name: Name, rawowner: Symbol | Null) extends DeclaringSymbol(name, rawowner) {
    private[tastyquery] var initialised: Boolean = false
  }

  // TODO: typename or term name?
  class PackageClassSymbol(override val name: Name, rawowner: PackageClassSymbol | Null)
      extends ClassSymbol(name, rawowner) {
    if (rawowner != null) {
      // A package symbol is always a declaration in its owner package
      rawowner.addDecl(this)
    } else {
      // Root package is the only symbol that is allowed to not have an owner
      assert(name == nme.RootName)
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
