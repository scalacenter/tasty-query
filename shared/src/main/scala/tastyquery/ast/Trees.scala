package tastyquery.ast

import tastyquery.ast.Constants.Constant
import tastyquery.ast.Names.{Name, TermName, TypeName}
import tastyquery.ast.Types.{Type, TypeBounds}
import tastyquery.ast.TypeTrees.*
import tastyquery.ast.Symbols.{ClassSymbol, NoSymbol, PackageClassSymbol, RegularSymbol, Symbol}

object Trees {

  abstract class Tree

  trait DefTree(val symbol: Symbol)

  case class PackageDef(pid: PackageClassSymbol, stats: List[Tree]) extends Tree with DefTree(pid)

  case class ImportSelector(imported: Ident, renamed: Tree = EmptyTree, bound: TypeTree = EmptyTypeTree) extends Tree {

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

  /** import expr.selectors */
  case class Export(expr: Tree, selectors: List[ImportSelector]) extends Tree

  /** mods class name template     or
    *  mods trait name template     or
    *  mods type name = rhs   or
    *  mods type name >: lo <: hi,          if rhs = TypeBoundsTree(lo, hi)      or
    *  mods type name >: lo <: hi = rhs     if rhs = TypeBoundsTree(lo, hi, alias) and opaque in mods
    */
  abstract class TypeDef(name: TypeName, override val symbol: Symbol) extends Tree with DefTree(symbol)

  case class Class(name: TypeName, rhs: Template, override val symbol: ClassSymbol) extends TypeDef(name, symbol)

  /** A type member has a type tree rhs if the member is defined by the user, or typebounds if it's synthetic */
  case class TypeMember(name: TypeName, rhs: TypeTree | TypeBounds, override val symbol: RegularSymbol)
      extends TypeDef(name, symbol)

  /** The bounds are a type tree if the method is defined by the user and bounds-only if it's synthetic */
  case class TypeParam(
    name: TypeName,
    bounds: TypeBoundsTree | TypeBounds | TypeLambdaTree,
    override val symbol: RegularSymbol
  ) extends TypeDef(name, symbol)

  /** extends parents { self => body }
    *
    * @param classParent -- the parent whose constructor is called.
    *                       If the template defines a class, this is its only class parent.
    * @param parents        trait parents of the template and the class parent if the template defines a trait.
    */
  case class Template(constr: DefDef, parents: List[Apply | Block | TypeTree], self: ValDef, body: List[Tree])
      extends Tree

  /** mods val name: tpt = rhs */
  case class ValDef(name: TermName, tpt: TypeTree, rhs: Tree, override val symbol: RegularSymbol)
      extends Tree
      with DefTree(symbol)

  type ParamsClause = List[ValDef] | List[TypeParam]

  /** mods def name[tparams](vparams_1)...(vparams_n): tpt = rhs */
  case class DefDef(
    name: TermName,
    params: List[ParamsClause],
    tpt: TypeTree,
    rhs: Tree,
    override val symbol: RegularSymbol
  ) extends Tree
      with DefTree(symbol)

  /** name */
  case class Ident(name: TermName) extends Tree

  /** reference to a package, seen as a term */
  class ReferencedPackage(override val name: TermName) extends Ident(name) {
    override def toString: String = s"ReferencedPackage($name)"
  }

  object ReferencedPackage {
    def unapply(r: ReferencedPackage): Option[TermName] = Some(r.name)
  }

  /** qualifier.termName */
  case class Select(qualifier: Tree, name: TermName) extends Tree

  /** qual.this */
  case class This(qualifier: Option[TypeIdent]) extends Tree

  /** C.super[mix], where qual = C.this */
  case class Super(qual: Tree, mix: Option[TypeIdent]) extends Tree

  /** fun(args) */
  case class Apply(fun: Tree, args: List[Tree]) extends Tree

  /** fun[args] */
  case class TypeApply(fun: Tree, args: List[TypeTree]) extends Tree

  /** new tpt, but no constructor call */
  case class New(tpt: TypeTree) extends Tree

  /** expr : tpt */
  case class Typed(expr: Tree, tpt: TypeTree) extends Tree

  /** name = arg, outside a parameter list */
  case class Assign(lhs: Tree, rhs: Tree) extends Tree

  /** name = arg, in a parameter list */
  case class NamedArg(name: Name, arg: Tree) extends Tree

  /** { stats; expr } */
  case class Block(stats: List[Tree], expr: Tree) extends Tree

  /** if cond then thenp else elsep */
  case class If(cond: Tree, thenPart: Tree, elsePart: Tree) extends Tree {
    def isInline = false
  }
  class InlineIf(cond: Tree, thenPart: Tree, elsePart: Tree) extends If(cond, thenPart, elsePart) {
    override def isInline = true
    override def toString = s"InlineIf($cond, $thenPart, $elsePart)"
  }

  /**  @param meth   A reference to the method.
    *  @param tpt    Not an EmptyTree only if the lambda's type is a SAMtype rather than a function type.
    */
  case class Lambda(meth: Tree, tpt: TypeTree) extends Tree

  /** selector match { cases } */
  case class Match(selector: Tree, cases: List[CaseDef]) extends Tree {
    def isInline = false
  }
  class InlineMatch(selector: Tree, cases: List[CaseDef]) extends Match(selector, cases) {
    override def isInline = true
    override def toString = s"InlineMatch($selector, $cases)"
  }

  /** case pattern if guard => body; only appears as child of a Match and Try */
  case class CaseDef(pattern: Tree, guard: Tree, body: Tree) extends Tree

  /** pattern in {@link Unapply} */
  case class Bind(name: Name, body: Tree, override val symbol: RegularSymbol) extends Tree with DefTree(symbol)

  /** tree_1 | ... | tree_n */
  case class Alternative(trees: List[Tree]) extends Tree

  /** `extractor(patterns)` in a pattern:
    *  @param fun       is `extractor.unapply` (or, for backwards compatibility, `extractor.unapplySeq`)
    *                   possibly with type parameters
    *  @param implicits Any implicit parameters passed to the unapply after the selector
    *  @param patterns  The argument patterns in the pattern match.
    *
    *  It is typed with same type as first `fun` argument
    *  Given a match selector `sel` a pattern UnApply(fun, implicits, patterns) is roughly translated as follows
    *
    *    val result = fun(sel)(implicits)
    *    if (result.isDefined) "match patterns against result"
    */
  case class Unapply(fun: Tree, implicits: List[Tree], patterns: List[Tree]) extends Tree

  /** Seq(elems)
    *  @param  tpt  The element type of the sequence.
    */
  case class SeqLiteral(elems: List[Tree], elemtpt: TypeTree) extends Tree

  /** while (cond) { body } */
  case class While(cond: Tree, body: Tree) extends Tree

  /** throw expr */
  case class Throw(expr: Tree) extends Tree

  /** try block catch cases finally finalizer */
  case class Try(expr: Tree, cases: List[CaseDef], finalizer: Tree) extends Tree

  case class Literal(constant: Constant) extends Tree

  case class Return(expr: Tree, from: Tree) extends Tree

  /** A tree representing inlined code.
    *
    * @param expr
    *   The inlined tree, minus bindings.
    * @param caller
    *   The toplevel class from which the call was inlined.
    * @param bindings
    *   Bindings for proxies to be used in the inlined code
    *
    * The full inlined code is equivalent to
    *
    * { bindings; expr }
    */
  case class Inlined(expr: Tree, caller: TypeIdent, bindings: List[Tree]) extends Tree

  case object EmptyTree extends Tree

  val EmptyValDef: ValDef = ValDef(Names.Wildcard, EmptyTypeTree, EmptyTree, NoSymbol)
}
