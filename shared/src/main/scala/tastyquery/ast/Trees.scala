package tastyquery.ast

import tastyquery.ast.Constants.Constant
import tastyquery.ast.Names.{Name, TermName, TypeName}
import tastyquery.ast.Types.Type
import tastyquery.ast.Symbols.Symbol

object Trees {

  abstract class Tree

  case class PackageDef(pid: Symbol, stats: List[Tree]) extends Tree

  case class ImportSelector(imported: Ident, renamed: Tree = EmptyTree, bound: Tree = EmptyTree) extends Tree {

    /** It's a `given` selector */
    val isGiven: Boolean = imported.name.isEmpty

    /** It's a `given` or `_` selector */
    val isWildcard: Boolean = isGiven || imported.name == Names.Wildcard

    /** The imported name, EmptyTermName if it's a given selector */
    val name: TermName = imported.name.asInstanceOf[TermName]

    /** The renamed part (which might be `_`), if present, or `name`, if missing */
    val rename: TermName = renamed match {
      case Ident(rename: TermName) => rename
      case _                       => name
    }
  }

  case class Import(expr: Tree, selectors: List[ImportSelector]) extends Tree

  /**
   * mods class name template     or
   *  mods trait name template     or
   *  mods type name = rhs   or
   *  mods type name >: lo <: hi,          if rhs = TypeBoundsTree(lo, hi)      or
   *  mods type name >: lo <: hi = rhs     if rhs = TypeBoundsTree(lo, hi, alias) and opaque in mods
   */
  case class TypeDef(name: TypeName, rhs: Tree) extends Tree

  /** extends parents { self => body } */
  case class Template(constr: DefDef, parents: List[Tree], self: ValDef, body: List[Tree]) extends Tree

  /** mods val name: tpt = rhs */
  case class ValDef(name: TermName, tpt: Tree, rhs: Tree) extends Tree

  /** mods def name[tparams](vparams_1)...(vparams_n): tpt = rhs */
  case class DefDef(name: TermName, tparams: List[TypeDef], vparamss: List[List[ValDef]], tpt: Tree, rhs: Tree)
      extends Tree

  /** name */
  case class Ident(name: Name) extends Tree

  /** qualifier.name, or qualifier#name, if qualifier is a type */
  case class Select(qualifier: Tree, name: Name) extends Tree

  /** fun(args) */
  case class Apply(fun: Tree, args: List[Tree]) extends Tree

  /** new tpt, but no constructor call */
  case class New(tpt: Tree) extends Tree

  case class Literal(constant: Constant) extends Tree

  case object EmptyTree extends Tree

  val EmptyValDef: ValDef = ValDef(Names.Wildcard, EmptyTree, EmptyTree)

  case class TypeTree(tp: Type) extends Tree

  // A marker for Trees or components which are not yet constructed correctly
  case class DummyTree[T <: Object](components: T, todo: String) extends Tree
}
