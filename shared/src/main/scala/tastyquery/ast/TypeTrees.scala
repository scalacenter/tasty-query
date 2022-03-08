package tastyquery.ast

import tastyquery.ast.Names.{nme, TypeName}
import tastyquery.ast.Symbols.RegularSymbol
import tastyquery.ast.Trees.{DefTree, Tree, TypeParam}
import tastyquery.ast.Types.{Type, TypeBounds, NoType}
import tastyquery.util.syntax.chaining.given

object TypeTrees {
  class TypeTreeToTypeError(val typeTree: TypeTree) extends RuntimeException(s"Could not convert $typeTree to type")

  object TypeTreeToTypeError {
    def unapply(e: TypeTreeToTypeError): Option[TypeTree] = Some(e.typeTree)
  }

  abstract class TypeTree {
    protected var myType: Type | Null = null

    protected def calculateType: Type = throw new TypeTreeToTypeError(this)
    final def toType: Type = {
      val local = myType
      if local == null then calculateType.useWith { myType = _ }
      else local
    }
  }

  case class TypeIdent(name: TypeName)(tpe: Type) extends TypeTree {
    myType = tpe
  }

  object EmptyTypeIdent extends TypeIdent(nme.EmptyTypeName)(NoType)

  case class TypeWrapper(tp: Type) extends TypeTree {
    override protected def calculateType: Type = tp
  }

  /** ref.type */
  case class SingletonTypeTree(ref: Tree) extends TypeTree

  case class RefinedTypeTree(underlying: TypeTree, refinements: List[Tree]) extends TypeTree

  /** => T */
  case class ByNameTypeTree(result: TypeTree) extends TypeTree

  /** tpt[args]
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

  case class TypeTreeBind(name: TypeName, body: TypeTree, override val symbol: RegularSymbol)
      extends TypeTree
      with DefTree(symbol)

  case object EmptyTypeTree extends TypeTree

  case class TypeBoundsTree(low: TypeTree, high: TypeTree)

  /** >: lo <: hi
    *  >: lo <: hi = alias  for RHS of bounded opaque type
    */
  case class BoundedTypeTree(bounds: TypeBoundsTree, alias: TypeTree) extends TypeTree
  case class NamedTypeBoundsTree(name: TypeName, bounds: TypeBounds) extends TypeTree

  case class TypeLambdaTree(tparams: List[TypeParam], body: TypeTree) extends TypeTree
}
