package tastyquery.ast

import tastyquery.ast.Names.TypeName
import tastyquery.ast.Trees.Tree
import tastyquery.ast.Types.Type

object TypeTrees {
  abstract class TypeTree

  case class TypeIdent(name: TypeName) extends TypeTree

  case class TypeWrapper(tp: Type) extends TypeTree

  /** ref.type */
  case class SingletonTypeTree(ref: Tree) extends TypeTree

  /** tpt[args] */
  case class AppliedTypeTree(tycon: TypeTree, args: List[TypeTree]) extends TypeTree

  case object EmptyTypeTree extends TypeTree
}
