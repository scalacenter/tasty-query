package tastyquery.ast

import tastyquery.ast.Names.{EmptyTermName, EmptyTypeName, TypeName}
import tastyquery.ast.Trees.{Tree, TypeParam}
import tastyquery.ast.Types.Type

object TypeTrees {
  abstract class TypeTree

  case class TypeIdent(name: TypeName) extends TypeTree

  object EmptyTypeIdent extends TypeIdent(EmptyTypeName)

  case class TypeWrapper(tp: Type) extends TypeTree

  /** ref.type */
  case class SingletonTypeTree(ref: Tree) extends TypeTree

  /** => T */
  case class ByNameTypeTree(result: TypeTree) extends TypeTree

  /** tpt[args] */
  case class AppliedTypeTree(tycon: TypeTree, args: List[TypeTree]) extends TypeTree

  // TODO: shouldn't qualifier be a type tree?
  /** qualifier#name */
  case class SelectTypeTree(qualifier: Tree, name: TypeName) extends TypeTree

  case object EmptyTypeTree extends TypeTree

  case class TypeBoundsTree(low: TypeTree, high: TypeTree)

  /**
   * >: lo <: hi
   *  >: lo <: hi = alias  for RHS of bounded opaque type
   */
  case class BoundedTypeTree(bounds: TypeBoundsTree, alias: TypeTree) extends TypeTree

  case class TypeLambdaTree(tparams: List[TypeParam], body: TypeTree) extends TypeTree
}
