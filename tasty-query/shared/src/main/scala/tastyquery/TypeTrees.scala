package tastyquery

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Spans.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

object TypeTrees {
  sealed abstract class TypeTree(val span: Span) {
    private var myType: Type | Null = null

    protected def calculateType(using Context): Type

    def withSpan(span: Span): TypeTree

    final def toType(using Context): Type = {
      val local = myType
      if local == null then
        val computed = calculateType
        myType = calculateType
        computed
      else local
    }
  }

  final case class TypeIdent(name: TypeName)(tpe: Type)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      tpe

    override final def withSpan(span: Span): TypeIdent = TypeIdent(name)(tpe)(span)
  }

  final case class TypeWrapper(tp: Type)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type = tp

    override final def withSpan(span: Span): TypeWrapper = TypeWrapper(tp)(span)
  }

  /** ref.type */
  final case class SingletonTypeTree(ref: TermTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      ref.tpe

    override final def withSpan(span: Span): SingletonTypeTree = SingletonTypeTree(ref)(span)
  }

  final case class RefinedTypeTree(underlying: TypeTree, refinements: List[Tree], refinedCls: ClassSymbol)(span: Span)
      extends TypeTree(span) {

    override protected def calculateType(using Context): Type =
      underlying.toType // TODO Actually take the refinements into account

    override final def withSpan(span: Span): RefinedTypeTree =
      RefinedTypeTree(underlying, refinements, refinedCls)(span)
  }

  /** => T */
  final case class ByNameTypeTree(result: TypeTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      ExprType(result.toType)

    override final def withSpan(span: Span): ByNameTypeTree = ByNameTypeTree(result)(span)
  }

  /** tpt[args]
    * TypeBounds[Tree] for wildcard application: tpt[_], tpt[?]
    */
  final case class AppliedTypeTree(tycon: TypeTree, args: List[TypeTree])(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      AppliedType(tycon.toType, args.map(_.toType))

    override final def withSpan(span: Span): AppliedTypeTree = AppliedTypeTree(tycon, args)(span)
  }

  /** qualifier#name */
  final case class SelectTypeTree(qualifier: TypeTree, name: TypeName)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      TypeRef(qualifier.toType, name)

    override final def withSpan(span: Span): SelectTypeTree = SelectTypeTree(qualifier, name)(span)
  }

  /** qualifier.name */
  final case class TermRefTypeTree(qualifier: TermTree, name: TermName)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      NamedType.possibleSelFromPackage(qualifier.tpe, name)

    override final def withSpan(span: Span): TermRefTypeTree = TermRefTypeTree(qualifier, name)(span)
  }

  /** arg @annot */
  final case class AnnotatedTypeTree(tpt: TypeTree, annotation: Tree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      AnnotatedType(tpt.toType, annotation)

    override final def withSpan(span: Span): AnnotatedTypeTree = AnnotatedTypeTree(tpt, annotation)(span)
  }

  /** [bound] selector match { cases } */
  final case class MatchTypeTree(bound: Option[TypeTree], selector: TypeTree, cases: List[TypeCaseDef])(span: Span)
      extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      defn.NothingType // TODO

    override final def withSpan(span: Span): MatchTypeTree = MatchTypeTree(bound, selector, cases)(span)
  }

  final case class TypeCaseDef(pattern: TypeTree, body: TypeTree)

  final case class TypeTreeBind(name: TypeName, body: TypeTree, override val symbol: LocalTypeParamSymbol)(span: Span)
      extends TypeTree(span)
      with DefTree(symbol) {
    override protected def calculateType(using Context): Type =
      TypeRef(NoType, symbol)

    override final def withSpan(span: Span): TypeTreeBind = TypeTreeBind(name, body, symbol)(span)
  }

  final case class TypeBoundsTree(low: TypeTree, high: TypeTree) {
    def toTypeBounds(using Context): TypeBounds =
      RealTypeBounds(low.toType, high.toType)
  }

  /** >: lo <: hi
    *  >: lo <: hi = alias  for RHS of bounded opaque type
    */
  final case class BoundedTypeTree(bounds: TypeBoundsTree, alias: Option[TypeTree])(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      BoundedType(bounds.toTypeBounds, alias.map(_.toType))

    override final def withSpan(span: Span): BoundedTypeTree = BoundedTypeTree(bounds, alias)(span)
  }

  final case class NamedTypeBoundsTree(name: TypeName, bounds: TypeBounds)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      NamedTypeBounds(name, bounds)

    override final def withSpan(span: Span): NamedTypeBoundsTree = NamedTypeBoundsTree(name, bounds)(span)
  }

  final case class WildcardTypeBoundsTree(bounds: TypeBoundsTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      WildcardTypeBounds(bounds.toTypeBounds)

    override final def withSpan(span: Span): WildcardTypeBoundsTree =
      WildcardTypeBoundsTree(bounds)(span)
  }

  final case class TypeLambdaTree(tparams: List[TypeParam], body: TypeTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      TypeLambda.fromParams(tparams)(tl => tl.integrate(tparams.map(_.symbol), body.toType))

    override final def withSpan(span: Span): TypeLambdaTree = TypeLambdaTree(tparams, body)(span)
  }
}
