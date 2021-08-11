package tastyquery.ast

import tastyquery.ast.Names.{EmptyTermName, EmptyTypeName, TypeName}
import tastyquery.ast.Trees.{Tree, TypeParam}
import tastyquery.ast.Types.{Type, TypeBounds}

object TypeTrees {
  abstract class TypeTree

  case class TypeIdent(name: TypeName) extends TypeTree

  object EmptyTypeIdent extends TypeIdent(EmptyTypeName)

  case class TypeWrapper(tp: Type) extends TypeTree

  /** ref.type */
  case class SingletonTypeTree(ref: Tree) extends TypeTree

  case class RefinedTypeTree(underlying: TypeTree, refinements: List[Tree]) extends TypeTree

  /** => T */
  case class ByNameTypeTree(result: TypeTree) extends TypeTree

  /**
   * tpt[args]
   * TypeBounds[Tree] for wildcard application: tpt[_], tpt[?]
   */
  case class AppliedTypeTree(tycon: TypeTree, args: List[TypeTree | TypeBoundsTree | TypeBounds]) extends TypeTree

  /** qualifier#name */
  case class SelectTypeTree(qualifier: TypeTree, name: TypeName) extends TypeTree

  /** qualifier.TypeName */
  case class SelectTypeFromTerm(qualifier: Tree, name: TypeName) extends TypeTree

  /** arg @annot */
  case class AnnotatedTypeTree(tpt: TypeTree, annotation: Tree) extends TypeTree

  /** [bound] selector match { cases } */
  case class MatchTypeTree(bound: TypeTree, selector: TypeTree, cases: List[TypeCaseDef]) extends TypeTree

  case class TypeCaseDef(pattern: TypeTree, body: TypeTree)

  case class TypeTreeBind(name: TypeName, body: TypeTree) extends TypeTree

  case object EmptyTypeTree extends TypeTree

  case class TypeBoundsTree(low: TypeTree, high: TypeTree)

  /**
   * >: lo <: hi
   *  >: lo <: hi = alias  for RHS of bounded opaque type
   */
  case class BoundedTypeTree(bounds: TypeBoundsTree, alias: TypeTree) extends TypeTree

  case class TypeLambdaTree(tparams: List[TypeParam], body: TypeTree) extends TypeTree
}
