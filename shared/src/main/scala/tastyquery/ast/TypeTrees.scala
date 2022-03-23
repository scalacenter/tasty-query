package tastyquery.ast

import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.RegularSymbol
import tastyquery.ast.Trees.{DefTree, Tree, TypeParam}
import tastyquery.ast.Types.*
import tastyquery.ast.Spans.{Span, NoSpan}
import tastyquery.util.syntax.chaining.given
import tastyquery.Contexts.BaseContext

object TypeTrees {
  class TypeTreeToTypeError(val typeTree: TypeTree) extends RuntimeException(s"Could not convert $typeTree to type")

  object TypeTreeToTypeError {
    def unapply(e: TypeTreeToTypeError): Option[TypeTree] = Some(e.typeTree)
  }

  abstract class TypeTree(val span: Span) {
    private var myType: Type | Null = null

    protected def calculateType(using BaseContext): Type

    final def toType(using BaseContext): Type = {
      val local = myType
      if local == null then calculateType.useWith { myType = _ }
      else local
    }
  }

  case class TypeIdent(name: TypeName)(tpe: Type)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type =
      tpe
  }

  object EmptyTypeIdent extends TypeIdent(nme.EmptyTypeName)(NoType)(NoSpan)

  case class TypeWrapper(tp: Type)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type = tp
  }

  /** ref.type */
  case class SingletonTypeTree(ref: Tree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type =
      ref.tpe
  }

  case class RefinedTypeTree(underlying: TypeTree, refinements: List[Tree])(span: Span) extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type =
      throw new TypeTreeToTypeError(this) // TODO
  }

  /** => T */
  case class ByNameTypeTree(result: TypeTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type =
      ExprType(result.toType)
  }

  /** tpt[args]
    * TypeBounds[Tree] for wildcard application: tpt[_], tpt[?]
    */
  case class AppliedTypeTree(tycon: TypeTree, args: List[TypeTree | TypeBoundsTree | TypeBounds])(span: Span)
      extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type =
      AppliedType(
        tycon.toType,
        args.map {
          case arg: TypeTree       => arg.toType
          case arg: TypeBoundsTree => arg.toTypeBounds
          case arg: TypeBounds     => arg
        }
      )
  }

  /** qualifier#name */
  case class SelectTypeTree(qualifier: TypeTree, name: TypeName)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type =
      TypeRef(qualifier.toType, name)
  }

  /** qualifier.name */
  case class TermRefTypeTree(qualifier: Tree, name: TermName)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type =
      TermRef(qualifier.tpe, name)
  }

  /** arg @annot */
  case class AnnotatedTypeTree(tpt: TypeTree, annotation: Tree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type =
      AnnotatedType(tpt.toType, annotation)
  }

  /** [bound] selector match { cases } */
  case class MatchTypeTree(bound: TypeTree, selector: TypeTree, cases: List[TypeCaseDef])(span: Span)
      extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type =
      throw new TypeTreeToTypeError(this) // TODO
  }

  case class TypeCaseDef(pattern: TypeTree, body: TypeTree)

  case class TypeTreeBind(name: TypeName, body: TypeTree, override val symbol: RegularSymbol)(span: Span)
      extends TypeTree(span)
      with DefTree(symbol) {
    override protected def calculateType(using BaseContext): Type =
      TermRef(NoType, symbol)
  }

  case object EmptyTypeTree extends TypeTree(NoSpan) {
    override protected def calculateType(using BaseContext): Type =
      NoType
  }

  case class TypeBoundsTree(low: TypeTree, high: TypeTree) {
    def toTypeBounds(using BaseContext): TypeBounds =
      RealTypeBounds(low.toType, high.toType)
  }

  /** >: lo <: hi
    *  >: lo <: hi = alias  for RHS of bounded opaque type
    */
  case class BoundedTypeTree(bounds: TypeBoundsTree, alias: TypeTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type =
      BoundedType(bounds.toTypeBounds, alias.toType)
  }

  case class NamedTypeBoundsTree(name: TypeName, bounds: TypeBounds)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type =
      NamedTypeBounds(name, bounds)
  }

  case class TypeLambdaTree(tparams: List[TypeParam], body: TypeTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using BaseContext): Type =
      TypeLambda(tparams)(_ => body.toType)
  }
}
