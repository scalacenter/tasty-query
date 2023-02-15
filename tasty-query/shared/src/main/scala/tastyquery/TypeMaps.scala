package tastyquery

import scala.collection.mutable

import tastyquery.Annotations.*
import tastyquery.Contexts.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

private[tastyquery] object TypeMaps {

  /** Common base class of TypeMap and TypeAccumulator */
  abstract class VariantTraversal:
    protected var variance: Int = 1

    inline protected def atVariance[T](v: Int)(op: => T): T = {
      val saved = variance
      variance = v
      val res = op
      variance = saved
      res
    }
  end VariantTraversal

  abstract class TypeMap extends VariantTraversal with (Type => Type) {
    thisMap =>

    final def apply(tp: TypeMappable): tp.ThisTypeMappableType =
      // Unfortunately, GADT reasoning is not smart enough to refine the type of `tp`
      tp match
        case tp2: Type =>
          val result: tp2.ThisTypeMappableType = apply(tp2)
          result.asInstanceOf[tp.ThisTypeMappableType]
        case tp2: TypeBounds =>
          val result: tp2.ThisTypeMappableType = apply(tp2)
          result.asInstanceOf[tp.ThisTypeMappableType]
        case NoPrefix =>
          tp.asInstanceOf[tp.ThisTypeMappableType]

    def apply(tp: Type): Type

    def apply(bounds: TypeBounds): TypeBounds =
      mapOver(bounds)

    protected def derivedSelect(tp: NamedType, pre: Type): Type =
      tp.derivedSelect(pre)
    protected def derivedTypeRefinement(tp: TypeRefinement, parent: Type, refinedBounds: TypeBounds): Type =
      tp.derivedTypeRefinement(parent, tp.refinedName, refinedBounds)
    protected def derivedTermRefinement(tp: TermRefinement, parent: Type, refinedType: Type): Type =
      tp.derivedTermRefinement(parent, tp.refinedName, refinedType)
    protected def derivedWildcardTypeBounds(tp: WildcardTypeBounds, bounds: TypeBounds): Type =
      tp.derivedWildcardTypeBounds(bounds)
    protected def derivedAppliedType(tp: AppliedType, tycon: Type, args: List[Type]): Type =
      tp.derivedAppliedType(tycon, args)
    protected def derivedAndType(tp: AndType, tp1: Type, tp2: Type): Type =
      tp.derivedAndType(tp1, tp2)
    protected def derivedOrType(tp: OrType, tp1: Type, tp2: Type): Type =
      tp.derivedOrType(tp1, tp2)
    protected def derivedAnnotatedType(tp: AnnotatedType, underlying: Type, annot: Annotation): Type =
      tp.derivedAnnotatedType(underlying, annot)
    protected def derivedByNameType(tp: ByNameType, restpe: Type): Type =
      tp.derivedByNameType(restpe)
    protected def derivedLambdaType(tp: LambdaType, formals: List[tp.PInfo], restpe: Type): Type =
      tp.derivedLambdaType(tp.paramNames, formals, restpe)

    protected def derivedTypeAlias(tp: TypeAlias, alias: Type): TypeBounds =
      tp.derivedTypeAlias(alias)
    protected def derivedTypeBounds(bounds: TypeBounds, low: Type, high: Type): TypeBounds =
      bounds.derivedTypeBounds(low, high)

    protected def mapOverLambda(tp: LambdaType): Type =
      val restpe = tp.resultType
      val saved = variance
      variance = -variance
      val ptypes1 = tp.paramInfos.mapConserve(pi => apply(pi)).asInstanceOf[List[tp.PInfo]]
      variance = saved
      derivedLambdaType(tp, ptypes1, this(restpe))

    def isRange(tp: Type): Boolean = tp.isInstanceOf[Range]

    /** Map this function over given type */
    def mapOver(tp: Type): Type =
      tp match {
        case tp: NamedType =>
          // A prefix is never contravariant. Even if say `p.A` is used in a contravariant
          // context, we cannot assume contravariance for `p` because `p`'s lower
          // bound might not have a binding for `A` (e.g. the lower bound could be `Nothing`).
          // By contrast, covariance does translate to the prefix, since we have that
          // if `p <: q` then `p.A <: q.A`, and well-formedness requires that `A` is a member
          // of `p`'s upper bound.
          tp.prefix match
            case NoPrefix =>
              tp
            case prefix: Type =>
              val prefix1 = atVariance(variance max 0)(this(prefix))
              derivedSelect(tp, prefix1)

        case tp: AppliedType =>
          tp.map(this)

        case tp: LambdaType =>
          mapOverLambda(tp)

        case tp: WildcardTypeBounds =>
          derivedWildcardTypeBounds(tp, this(tp.bounds))

        case tp: ByNameType =>
          derivedByNameType(tp, this(tp.resultType))

        case tp: AnnotatedType =>
          derivedAnnotatedType(tp, this(tp.typ), tp.annotation) // tp.annotation.mapWith(this)

        case _: ThisType =>
          tp

        case tp: TypeRefinement =>
          derivedTypeRefinement(tp, this(tp.parent), this(tp.refinedBounds))

        case tp: TermRefinement =>
          derivedTermRefinement(tp, this(tp.parent), this(tp.refinedType))

        case tp: AndType =>
          derivedAndType(tp, this(tp.first), this(tp.second))

        case tp: OrType =>
          derivedOrType(tp, this(tp.first), this(tp.second))

        case _ =>
          tp
      }
    end mapOver

    def mapOver(bounds: TypeBounds): TypeBounds =
      bounds match
        case bounds: TypeAlias =>
          derivedTypeAlias(bounds, atVariance(0)(this(bounds.alias)))
        case _ =>
          variance = -variance
          val low1 = this(bounds.low)
          variance = -variance
          val high1 = this(bounds.high)
          derivedTypeBounds(bounds, low1, high1)
    end mapOver

    //def mapOver(syms: List[Symbol]): List[Symbol] = mapSymbols(syms, treeTypeMap)

    def andThen(f: Type => Type): TypeMap = new TypeMap {
      def apply(tp: Type): Type = f(thisMap(tp))
    }
  }

  abstract class NormalizingTypeMap(using Context) extends TypeMap:
    override protected def derivedSelect(tp: NamedType, pre: Type): Type =
      tp.normalizedDerivedSelect(pre)

    protected def mapArgs(args: List[Type], tparams: List[TypeParamInfo]): List[Type] = args match
      case arg :: otherArgs if tparams.nonEmpty =>
        val arg1 = arg match
          case arg: WildcardTypeBounds => this(arg)
          case arg                     => atVariance(variance * tparams.head.paramVariance.sign)(this(arg))
        val otherArgs1 = mapArgs(otherArgs, tparams.tail)
        if ((arg1 eq arg) && (otherArgs1 eq otherArgs)) args
        else arg1 :: otherArgs1
      case nil =>
        nil

    /** Map this function over given type */
    override def mapOver(tp: Type): Type =
      tp match
        case tp: AppliedType =>
          derivedAppliedType(tp, this(tp.tycon), mapArgs(tp.args, tp.tyconTypeParams))

        case _ =>
          super.mapOver(tp)
    end mapOver
  end NormalizingTypeMap

  /** A type map that approximates TypeBounds types depending on
    * variance.
    *
    * if variance > 0 : approximate by upper bound
    *    variance < 0 : approximate by lower bound
    *    variance = 0 : propagate bounds to next outer level
    */
  abstract class ApproximatingTypeMap(using Context) extends NormalizingTypeMap { thisMap =>

    protected def range(lo: Type, hi: Type): Type =
      if (variance > 0) hi
      else if (variance < 0) lo
      else if (lo `eq` hi) lo
      else Range(lower(lo), upper(hi))

    protected def emptyRange: Type = range(defn.NothingType, defn.AnyType)

    protected def lower(tp: Type): Type = tp match {
      case tp: Range => tp.lo
      case _         => tp
    }

    protected def upper(tp: Type): Type = tp match {
      case tp: Range => tp.hi
      case _         => tp
    }

    protected def rangeToBounds(tp: Type): Type = tp match {
      case Range(lo, hi) => WildcardTypeBounds(RealTypeBounds(lo, hi))
      case _             => tp
    }

    private var expandingBounds: Boolean = false

    /** Whether it is currently expanding bounds
      *
      * It is used to avoid following LazyRef in F-Bounds
      */
    def isExpandingBounds: Boolean = expandingBounds

    protected def expandBounds(tp: TypeBounds): Type =
      val saved = expandingBounds
      expandingBounds = true
      val res = range(atVariance(-variance)(reapply(tp.low)), reapply(tp.high))
      expandingBounds = saved
      res

    /** Try to widen a named type to its info relative to given prefix `pre`, where possible.
      * The possible cases are listed inline in the code.
      */
    def tryWiden(tp: NamedType, pre: Type): Option[Type] =
      pre.member(tp.name) match
        case memberSym: TypeMemberSymbol =>
          memberSym.typeDef match
            case TypeMemberDefinition.TypeAlias(alias) =>
              // if H#T = U, then for any x in L..H, x.T =:= U,
              // hence we can replace with U under all variances
              Some(reapply(alias))
            case _ =>
              // If H#T = ? >: S <: U, then for any x in L..H, S <: x.T <: U,
              // hence we can replace with S..U under all variances
              Some(expandBounds(memberSym.bounds))
        case memberSym: TermSymbol =>
          memberSym.declaredType.dealias match
            case tpe: SingletonType =>
              // if H#x: y.type, then for any x in L..H, x.type =:= y.type,
              // hence we can replace with y.type under all variances
              Some(reapply(tpe))
            case _ =>
              None
        case _ =>
          None
    end tryWiden

    /** Expand parameter reference corresponding to prefix `pre`;
      * If the expansion is a wildcard parameter reference, convert its
      * underlying bounds to a range, otherwise return the expansion.
      */
    def expandParam(tp: NamedType, pre: Type): Option[Type] =
      tp.argForParam(pre)
        .map(_ match {
          case arg: TypeRef if arg.prefix.isArgPrefixOf(arg.symbol) =>
            expandBounds(arg.symbol.asInstanceOf[ClassTypeParamSymbol].bounds)
          case arg: WildcardTypeBounds => expandBounds(arg.bounds)
          case arg                     => reapply(arg)
        })

    /** Derived selection.
      * @pre   the (upper bound of) prefix `pre` has a member named `tp.name`.
      */
    override protected def derivedSelect(tp: NamedType, pre: Type): Type =
      if (pre eq tp.prefix) tp
      else
        pre match {
          case Range(preLo, preHi) =>
            val forwarded =
              if (tp.symbol.isAllOf(ClassTypeParam)) expandParam(tp, preHi)
              else tryWiden(tp, preHi)
            forwarded.getOrElse {
              range(super.derivedSelect(tp, preLo).lowerBound, super.derivedSelect(tp, preHi).upperBound)
            }
          case _ =>
            super.derivedSelect(tp, pre) match {
              case tp: WildcardTypeBounds => range(tp.bounds.low, tp.bounds.high)
              case tp                     => tp
            }
        }

    /*override protected def derivedRefinedType(tp: RefinedType, parent: Type, info: Type): Type =
      if ((parent eq tp.parent) && (info eq tp.refinedInfo)) tp
      else parent match {
        case Range(parentLo, parentHi) =>
          range(derivedRefinedType(tp, parentLo, info), derivedRefinedType(tp, parentHi, info))
        case _ =>
          def propagate(lo: Type, hi: Type) =
            range(derivedRefinedType(tp, parent, lo), derivedRefinedType(tp, parent, hi))
          if (parent.isExactlyNothing) parent
          else info match {
            case Range(infoLo: TypeBounds, infoHi: TypeBounds) =>
              assert(variance == 0)
              if (!infoLo.isTypeAlias && !infoHi.isTypeAlias) propagate(infoLo, infoHi)
              else range(defn.NothingType, parent)
            case Range(infoLo, infoHi) =>
              propagate(infoLo, infoHi)
            case _ =>
              tp.derivedRefinedType(parent, tp.refinedName, info)
          }
      }*/

    /*override protected def derivedRecType(tp: RecType, parent: Type): Type =
      if (parent eq tp.parent) tp
      else parent match {
        case Range(lo, hi) => range(tp.rebind(lo), tp.rebind(hi))
        case _ => tp.rebind(parent)
      }*/

    override protected def derivedTypeAlias(tp: TypeAlias, alias: Type): TypeBounds =
      if (alias eq tp.alias) tp
      else
        alias match {
          case Range(lo, hi) =>
            if (variance > 0) RealTypeBounds(lo, hi)
            else TypeAlias(range(lo, hi))
          case _ => tp.derivedTypeAlias(alias)
        }

    override protected def derivedWildcardTypeBounds(tp: WildcardTypeBounds, bounds: TypeBounds): Type =
      if bounds eq tp.bounds then tp
      else if isRange(bounds.low) || isRange(bounds.high) then
        if variance > 0 then WildcardTypeBounds(RealTypeBounds(lower(bounds.low), upper(bounds.high)))
        else
          range(
            WildcardTypeBounds(RealTypeBounds(upper(bounds.low), lower(bounds.high))),
            WildcardTypeBounds(RealTypeBounds(lower(bounds.low), upper(bounds.high)))
          )
      else tp.derivedWildcardTypeBounds(bounds)

    /*override protected def derivedSuperType(tp: SuperType, thistp: Type, supertp: Type): Type =
      if (isRange(thistp) || isRange(supertp)) emptyRange
      else tp.derivedSuperType(thistp, supertp)*/

    override protected def derivedAppliedType(tp: AppliedType, tycon: Type, args: List[Type]): Type =
      tycon match {
        case Range(tyconLo, tyconHi) =>
          range(derivedAppliedType(tp, tyconLo, args), derivedAppliedType(tp, tyconHi, args))
        case _ =>
          if args.exists(isRange) then
            if variance > 0 then
              tp.derivedAppliedType(tycon, args.map(rangeToBounds)) match
                case tp1: AppliedType if tp1.isUnreducibleWild =>
                  // don't infer a type that would trigger an error later in
                  // Checking.checkAppliedType; fall through to default handling instead
                  ()
                case tp1 =>
                  return tp1
            end if
            val loBuf, hiBuf = new mutable.ListBuffer[Type]
            // Given `C[A1, ..., An]` where some A's are ranges, try to find
            // non-range arguments L1, ..., Ln and H1, ..., Hn such that
            // C[L1, ..., Ln] <: C[H1, ..., Hn] by taking the right limits of
            // ranges that appear in as co- or contravariant arguments.
            // Fail for non-variant argument ranges (see use-site else branch below).
            // If successful, the L-arguments are in loBut, the H-arguments in hiBuf.
            // @return  operation succeeded for all arguments.
            def distributeArgs(args: List[Type], tparams: List[TypeParamInfo]): Boolean = args match {
              case Range(lo, hi) :: args1 =>
                val v = tparams.head.paramVariance.sign
                if (v == 0) false
                else {
                  if (v > 0) { loBuf += lo; hiBuf += hi }
                  else { loBuf += hi; hiBuf += lo }
                  distributeArgs(args1, tparams.tail)
                }
              case arg :: args1 =>
                loBuf += arg; hiBuf += arg
                distributeArgs(args1, tparams.tail)
              case nil =>
                true
            }
            if (distributeArgs(args, tp.tyconTypeParams))
              range(tp.derivedAppliedType(tycon, loBuf.toList), tp.derivedAppliedType(tycon, hiBuf.toList))
            else if tycon.isLambdaSub || args.exists(isRangeOfNonTermTypes) then range(defn.NothingType, defn.AnyType)
            else
              // See lampepfl/dotty#14152
              range(defn.NothingType, tp.derivedAppliedType(tycon, args.map(rangeToBounds)))
          else tp.derivedAppliedType(tycon, args)
      }

    private def isRangeOfNonTermTypes(tp: Type): Boolean = tp match
      case Range(lo, hi) => !lo.isInstanceOf[TermType] || !hi.isInstanceOf[TermType]
      case _             => false

    override protected def derivedAndType(tp: AndType, tp1: Type, tp2: Type): Type =
      if (isRange(tp1) || isRange(tp2)) range(lower(tp1) & lower(tp2), upper(tp1) & upper(tp2))
      else tp.derivedAndType(tp1, tp2)

    override protected def derivedOrType(tp: OrType, tp1: Type, tp2: Type): Type =
      if (isRange(tp1) || isRange(tp2)) range(lower(tp1) | lower(tp2), upper(tp1) | upper(tp2))
      else tp.derivedOrType(tp1, tp2)

    /*override protected def derivedAnnotatedType(tp: AnnotatedType, underlying: Type, annot: Annotation): Type =
      underlying match {
        case Range(lo, hi) =>
          range(tp.derivedAnnotatedType(lo, annot), tp.derivedAnnotatedType(hi, annot))
        case _ =>
          if (underlying.isExactlyNothing) underlying
          else tp.derivedAnnotatedType(underlying, annot)
      }*/

    /*override protected def derivedMatchType(tp: MatchType, bound: Type, scrutinee: Type, cases: List[Type]): Type =
      bound match
        case Range(lo, hi) =>
          range(derivedMatchType(tp, lo, scrutinee, cases), derivedMatchType(tp, hi, scrutinee, cases))
        case _ =>
          scrutinee match
            case Range(lo, hi) => range(bound.bounds.lo, bound.bounds.hi)
            case _ =>
              if cases.exists(isRange) then
                Range(
                  tp.derivedMatchType(bound, scrutinee, cases.map(lower)),
                  tp.derivedMatchType(bound, scrutinee, cases.map(upper)))
              else
                tp.derivedMatchType(bound, scrutinee, cases)*/

    /*override protected def derivedSkolemType(tp: SkolemType, info: Type): Type =
      if info eq tp.info then tp
      // By definition, a skolem is neither a subtype nor a supertype of a
      // different skolem. So, regardless of `variance`, we cannot return a
      // fresh skolem when approximating an existing skolem, we can only return
      // a range.
      else range(defn.NothingType, info)*/

    /*override protected def derivedClassInfo(tp: ClassInfo, pre: Type): Type = {
      assert(!isRange(pre))
        // we don't know what to do here; this case has to be handled in subclasses
        // (typically by handling ClassInfo's specially, in case they can be encountered).
      tp.derivedClassInfo(pre)
    }*/

    /*override protected def derivedLambdaType(tp: LambdaType)(formals: List[tp.PInfo], restpe: Type): Type =
      restpe match {
        case Range(lo, hi) =>
          range(derivedLambdaType(tp)(formals, lo), derivedLambdaType(tp)(formals, hi))
        case _ =>
          if formals.exists(isRange) then
            range(
              derivedLambdaType(tp)(formals.map(upper(_).asInstanceOf[tp.PInfo]), restpe),
              derivedLambdaType(tp)(formals.map(lower(_).asInstanceOf[tp.PInfo]), restpe))
          else
            tp.derivedLambdaType(tp.paramNames, formals, restpe)
      }*/

    protected def reapply(tp: Type): Type = apply(tp)
  }

  /** A range of possible types between lower bound `lo` and upper bound `hi`.
    * Only used internally in `ApproximatingTypeMap`.
    */
  final case class Range(lo: Type, hi: Type) extends CustomTransientGroundType {
    assert(!lo.isInstanceOf[Range])
    assert(!hi.isInstanceOf[Range])
  }

}
