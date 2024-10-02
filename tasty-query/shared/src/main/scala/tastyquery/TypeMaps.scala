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

  abstract class TypeMap extends VariantTraversal {
    thisMap =>

    final def apply(tp: TypeMappable): tp.ThisTypeMappableType =
      transform(tp).asInstanceOf[tp.ThisTypeMappableType]

    protected def transform(tp: TypeMappable): TypeMappable

    protected def derivedSelect(tp: NamedType, pre: Type): Type =
      tp.derivedSelect(pre)
    protected def derivedRecType(tp: RecType, parent: Type): RecType =
      tp.derivedRecType(parent)
    protected def derivedTypeRefinement(tp: TypeRefinement, parent: Type, refinedBounds: TypeBounds): Type =
      tp.derivedTypeRefinement(parent, tp.refinedName, refinedBounds)
    protected def derivedTermRefinement(tp: TermRefinement, parent: Type, refinedType: TypeOrMethodic): Type =
      tp.derivedTermRefinement(parent, tp.refinedName, refinedType)
    protected def derivedWildcardTypeArg(tp: WildcardTypeArg, bounds: TypeBounds): WildcardTypeArg =
      tp.derivedWildcardTypeArg(bounds)
    protected def derivedAppliedType(tp: AppliedType, tycon: Type, args: List[TypeOrWildcard]): Type =
      tp.derivedAppliedType(tycon, args)
    protected def derivedAndType(tp: AndType, tp1: Type, tp2: Type): Type =
      tp.derivedAndType(tp1, tp2)
    protected def derivedOrType(tp: OrType, tp1: Type, tp2: Type): Type =
      tp.derivedOrType(tp1, tp2)
    protected def derivedAnnotatedType(tp: AnnotatedType, underlying: Type, annot: Annotation): Type =
      tp.derivedAnnotatedType(underlying, annot)
    protected def derivedMatchType(tp: MatchType, bound: Type, scrutinee: Type, cases: List[MatchTypeCase]): Type =
      tp.derivedMatchType(bound, scrutinee, cases)
    protected def derivedFlexibleType(tp: FlexibleType, nonNullableType: Type): Type =
      tp.derivedFlexibleType(nonNullableType)
    protected def derivedByNameType(tp: ByNameType, restpe: Type): Type =
      tp.derivedByNameType(restpe)
    protected def derivedRepeatedType(tp: RepeatedType, elemType: Type): Type =
      tp.derivedRepeatedType(elemType)
    protected def derivedLambdaType(tp: LambdaType, formals: List[tp.PInfo], restpe: tp.ResultType): tp.This =
      tp.derivedLambdaType(tp.paramNames, formals, restpe)
    protected def derivedSkolemType(tp: SkolemType, tpe: Type): SkolemType =
      tp.derivedSkolemType(tpe)

    protected def derivedTypeAlias(tp: TypeAlias, alias: Type): TypeBounds =
      tp.derivedTypeAlias(alias)
    protected def derivedTypeBounds(bounds: TypeBounds, low: Type, high: Type): TypeBounds =
      bounds.derivedTypeBounds(low, high)

    protected def mapOverLambda(tp: LambdaType): tp.This =
      val restpe = tp.resultType
      val saved = variance
      variance = -variance
      val ptypes1 = tp.paramInfos.mapConserve(pi => apply(pi)).asInstanceOf[List[tp.PInfo]]
      variance = saved
      derivedLambdaType(tp, ptypes1, this(restpe).asInstanceOf[tp.ResultType])

    protected def mapOverMatchTypeCase(caze: MatchTypeCase): MatchTypeCase =
      caze.derivedMatchTypeCase(
        caze.paramTypeBounds.mapConserve(bounds => apply(bounds)),
        this(caze.pattern),
        this(caze.result)
      )
    end mapOverMatchTypeCase

    def isRange(tp: TypeOrWildcard): Boolean = tp.isInstanceOf[Range]

    final def mapOver(tp: TypeMappable): tp.ThisTypeMappableType =
      val result: TypeMappable = tp match
        case tp: Type            => mapOver(tp): tp.ThisTypeMappableType
        case tp: TypeBounds      => mapOver(tp): tp.ThisTypeMappableType
        case tp: LambdaType      => mapOverLambda(tp): tp.ThisTypeMappableType
        case tp: WildcardTypeArg => derivedWildcardTypeArg(tp, this(tp.bounds)): tp.ThisTypeMappableType
        case tp @ NoPrefix       => tp: tp.ThisTypeMappableType
        case tp: PackageRef      => tp: tp.ThisTypeMappableType

      result.asInstanceOf[tp.ThisTypeMappableType]
    end mapOver

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
            case NoPrefix | _: PackageRef =>
              tp
            case prefix: Type =>
              val prefix1 = atVariance(variance max 0)(this(prefix))
              derivedSelect(tp, prefix1)

        case tp: AppliedType =>
          tp.map(this(_), this(_))

        case _: ThisType | _: SuperType | _: ConstantType | _: BoundType | _: NothingType | _: AnyKindType =>
          tp

        case tp: TypeLambda =>
          mapOverLambda(tp)

        case tp: FlexibleType =>
          derivedFlexibleType(tp, this(tp.nonNullableType))

        case tp: ByNameType =>
          derivedByNameType(tp, this(tp.resultType))

        case tp: RepeatedType =>
          derivedRepeatedType(tp, this(tp.elemType))

        case tp: AnnotatedType =>
          derivedAnnotatedType(tp, this(tp.typ), tp.annotation) // tp.annotation.mapWith(this)

        case tp: RecType =>
          derivedRecType(tp, this(tp.parent))

        case tp: TypeRefinement =>
          derivedTypeRefinement(tp, this(tp.parent), this(tp.refinedBounds))

        case tp: TermRefinement =>
          derivedTermRefinement(tp, this(tp.parent), this(tp.refinedType))

        case tp: AndType =>
          derivedAndType(tp, this(tp.first), this(tp.second))

        case tp: OrType =>
          derivedOrType(tp, this(tp.first), this(tp.second))

        case tp: MatchType =>
          // The spec says that all type positions in a match type are considered invariant
          atVariance(0) {
            val newBound = this(tp.bound)
            val newScrutinee = this(tp.scrutinee)
            val newCases = tp.cases.mapConserve(mapOverMatchTypeCase(_))
            derivedMatchType(tp, newBound, newScrutinee, newCases)
          }

        case tp: SkolemType =>
          derivedSkolemType(tp, this(tp.tpe))

        case _: CustomTransientGroundType =>
          throw UnsupportedOperationException(s"Cannot map over $tp")
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
  }

  abstract class NormalizingTypeMap(using Context) extends TypeMap:
    override protected def derivedSelect(tp: NamedType, pre: Type): Type =
      tp.normalizedDerivedSelect(pre)

    protected def mapArgs(args: List[TypeOrWildcard], tparams: List[TypeConstructorParam]): List[TypeOrWildcard] =
      args match
        case arg :: otherArgs if tparams.nonEmpty =>
          val arg1 = arg match
            case arg: WildcardTypeArg =>
              this(arg)
            case arg: Type =>
              /* `arg: TypeOrWildcard` allows the Type to be mapped to a WildcardTypeArg in this context.
               * Without it, we get a CCE that `WildcardTypeArg` cannot be cast to `Type`.
               */
              atVariance(variance * tparams.head.variance.sign)(this(arg: TypeOrWildcard))
          val otherArgs1 = mapArgs(otherArgs, tparams.tail)
          if ((arg1 eq arg) && (otherArgs1 eq otherArgs)) args
          else arg1 :: otherArgs1
        case nil =>
          nil
    end mapArgs

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

    protected def rangeToBounds(tp: TypeOrWildcard): TypeOrWildcard = tp match {
      case Range(lo, hi) => WildcardTypeArg(AbstractTypeBounds(lo, hi))
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
      pre.resolveMember(tp.name, pre) match
        case ResolveMemberResult.TypeMember(_, bounds) =>
          bounds match
            case TypeAlias(alias) =>
              // if H#T = U, then for any x in L..H, x.T =:= U,
              // hence we can replace with U under all variances
              Some(reapply(alias))
            case _ =>
              // If H#T = ? >: S <: U, then for any x in L..H, S <: x.T <: U,
              // hence we can replace with S..U under all variances
              Some(expandBounds(bounds))
        case ResolveMemberResult.TermMember(symbols, tpe, isStable) =>
          tpe.dealias match
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
    def expandParam(sym: ClassTypeParamSymbol, pre: Type): Option[Type] =
      sym
        .argForParam(pre)
        .map(_ match {
          case arg: TypeRef =>
            arg.optSymbol match
              case Some(argSym: ClassTypeParamSymbol) if arg.prefix.isArgPrefixOf(argSym) =>
                expandBounds(argSym.declaredBounds)
              case _ =>
                reapply(arg)
          case arg: WildcardTypeArg => expandBounds(arg.bounds)
          case arg: Type            => reapply(arg)
        })

    /** Derived selection.
      * @pre   the (upper bound of) prefix `pre` has a member named `tp.name`.
      */
    override protected def derivedSelect(tp: NamedType, pre: Type): Type =
      if (pre eq tp.prefix) tp
      else
        pre match {
          case Range(preLo, preHi) =>
            val forwarded = tp.optSymbol match
              case Some(sym: ClassTypeParamSymbol) => expandParam(sym, preHi)
              case _                               => tryWiden(tp, preHi)
            forwarded.getOrElse {
              /* TODO? We used to have `.lowerBound` and `.upperBound` on the
               * results of `super.derivedSelect`, coming from dotc. However
               * `super.derivedSelect` now statically returns a `Type`, so it
               * cannot be a wildcard. Maybe we need to reintroduce this in the
               * future.
               */
              range(super.derivedSelect(tp, preLo), super.derivedSelect(tp, preHi))
            }
          case _ =>
            /* TODO? Similar to the above. We used to translate a wildcard
             * received from `super.derivedSelect` into a `range`.
             */
            super.derivedSelect(tp, pre)
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
            if (variance > 0) AbstractTypeBounds(lo, hi)
            else TypeAlias(range(lo, hi))
          case _ => tp.derivedTypeAlias(alias)
        }

    override protected def derivedWildcardTypeArg(tp: WildcardTypeArg, bounds: TypeBounds): WildcardTypeArg =
      if bounds eq tp.bounds then tp
      else if isRange(bounds.low) || isRange(bounds.high) then
        if variance > 0 then WildcardTypeArg(AbstractTypeBounds(lower(bounds.low), upper(bounds.high)))
        else
          // TODO This makes no sense to me; one day we'll have to find a principled solution here
          WildcardTypeArg(
            AbstractTypeBounds(
              range(upper(bounds.low), lower(bounds.high)),
              range(lower(bounds.low), upper(bounds.high))
            )
          )
      else tp.derivedWildcardTypeArg(bounds)

    /*override protected def derivedSuperType(tp: SuperType, thistp: Type, supertp: Type): Type =
      if (isRange(thistp) || isRange(supertp)) emptyRange
      else tp.derivedSuperType(thistp, supertp)*/

    override protected def derivedAppliedType(tp: AppliedType, tycon: Type, args: List[TypeOrWildcard]): Type =
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
            def distributeArgs(args: List[TypeOrWildcard], tparams: List[TypeConstructorParam]): Boolean = args match {
              case Range(lo, hi) :: args1 =>
                val v = tparams.head.variance.sign
                if (v == 0) false
                else {
                  if (v > 0) { loBuf += lo; hiBuf += hi }
                  else { loBuf += hi; hiBuf += lo }
                  distributeArgs(args1, tparams.tail)
                }
              case arg :: args1 =>
                loBuf += arg.lowIfWildcard
                hiBuf += arg.highIfWildcard
                distributeArgs(args1, tparams.tail)
              case Nil =>
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

    private def isRangeOfNonTermTypes(tp: TypeOrWildcard): Boolean = tp match
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
