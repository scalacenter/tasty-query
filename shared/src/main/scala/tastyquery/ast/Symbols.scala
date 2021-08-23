package tastyquery.ast

import scala.collection.mutable
import tastyquery.ast.Names._

import dotty.tools.tasty.TastyFormat.NameTags

object Symbols {
  val NoSymbol = new Symbol(Names.EmptyTermName, null)

  class Symbol(val name: Name, val owner: Symbol) {
    override def toString: String = s"symbol[$name]"
  }

  object Symbol {
    def unapply(s: Symbol): Option[Name] = Some(s.name)
  }

  abstract class DeclaringSymbol(override val name: Name, override val owner: Symbol) extends Symbol(name, owner) {
    /* A map from the name of a declaration directly inside this symbol to the corresponding symbol
     * The qualifiers on the name are not dropped. For instance, the package names are always fully qualified. */
    protected val declarations: mutable.HashMap[Name, Symbol] = mutable.HashMap[Name, Symbol]()

    def addDecl(decl: Symbol): Unit         = declarations(decl.name) = decl
    def getDecl(name: Name): Option[Symbol] = declarations.get(name)
  }

  class MethodSymbol(override val name: TermName, override val owner: Symbol) extends DeclaringSymbol(name, owner)

  class ClassSymbol(override val name: Name, override val owner: Symbol) extends DeclaringSymbol(name, owner)

  // TODO: typename or term name?
  class PackageClassSymbol(override val name: Name, override val owner: Symbol) extends ClassSymbol(name, owner) {
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
  }
}
