package tastyquery

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Symbols.*
import tastyquery.Types.*
import tastyquery.TypeMaps.*

private[tastyquery] object Subtyping:
  def isSameType(tp1: Type, tp2: Type)(using Context): Boolean =
    isSubType(tp1, tp2) && isSubType(tp2, tp1)

  def isSubType(tp1: Type, tp2: Type)(using Context): Boolean =
    // `eq` is semantically important for identity-based types such as `TypeParamRef`
    (tp1 eq tp2) || level1(tp1, tp2)

  def isSubTypeOrMethodic(tp1: TypeOrMethodic, tp2: TypeOrMethodic)(using Context): Boolean = tp2 match
    case tp2: MethodType =>
      tp1 match
        case tp1: MethodType =>
          TypeOps.matchingMethodParams(tp1, tp2)
            && isSubTypeOrMethodic(tp1.resultType, Substituters.substBinders(tp2.resultType, tp2, tp1))
        case _ =>
          false

    case tp2: PolyType =>
      tp1 match
        case tp1: PolyType =>
          TypeOps.matchingPolyParams(tp1, tp2)
            && isSubTypeOrMethodic(tp1.resultType, Substituters.substBinders(tp2.resultType, tp2, tp1))
        case _ =>
          false

    case tp2: Type =>
      tp1 match
        case tp1: Type =>
          isSubType(tp1, tp2)
        case _ =>
          false
  end isSubTypeOrMethodic

  def isSubTypeArg(arg1: TypeOrWildcard, arg2: TypeOrWildcard, varianceSign: Int)(using Context): Boolean =
    varianceSign match
      case 1 =>
        isSubType(arg1.highIfWildcard, arg2.highIfWildcard)

      case -1 =>
        isSubType(arg2.lowIfWildcard, arg1.lowIfWildcard)

      case 0 =>
        arg2 match
          case arg2: WildcardTypeArg =>
            arg2.bounds.contains(arg1)
          case arg2: Type =>
            arg1 match
              case arg1: Type         => isSameType(arg1, arg2)
              case _: WildcardTypeArg => false
  end isSubTypeArg

  private def level1(tp1: Type, tp2: Type)(using Context): Boolean = tp2 match
    case tp2: AnyKindType =>
      true

    case tp2: TypeRef if tp2.isFromJavaObject =>
      isSubType(tp1, defn.AnyType)

    case tp2: TypeRef =>
      tp2.optAliasedType match
        case Some(alias) =>
          if isSubType(tp1, alias) then return true
        case None =>
          ()

      tp1 match
        case tp1: TypeRef =>
          tp1.optAliasedType match
            case Some(alias) =>
              if isSubType(alias, tp2) then return true
            case None =>
              ()
          level1NamedNamed(tp1, tp2)
        case _ =>
          level2(tp1, tp2)

    case tp2: TermRef =>
      tp1 match
        case tp1: TermRef => level1NamedNamed(tp1, tp2)
        case _            => level2(tp1, tp2)

    case tp2: ThisType =>
      val cls2 = tp2.cls
      tp1 match
        case tp1: ThisType =>
          tp1.cls == cls2
        case tp1: TypeRef if cls2.isModuleClass && tp1.isSpecificClass(cls2) =>
          (cls2.isStatic || isSubPrefix(tp1.prefix, cls2.localRef.prefix))
            || level2(tp1, tp2)
        case _ =>
          level2(tp1, tp2)

    case tp2: AndType =>
      isSubType(tp1, tp2.first) && isSubType(tp1, tp2.second)

    case tp2: ConstantType =>
      tp1 match
        case tp1: ConstantType =>
          tp1.value == tp2.value
        case _ =>
          level2(tp1, tp2)

    case tp2: AnnotatedType =>
      isSubType(tp1, tp2.typ)

    case _ =>
      level2(tp1, tp2)
  end level1

  private def level1NamedNamed(tp1: NamedType, tp2: NamedType)(using Context): Boolean =
    val sym1 = tp1.optSymbol
    val sym2 = tp2.optSymbol

    if sym1.isDefined && sym1 == sym2 then
      sym1.get.isStatic
      || isSubPrefix(tp1.prefix, tp2.prefix)
      || level2(tp1, tp2)
    else
      /* When the symbols are not the same, we could still have a subtyping
       * relationship if they are defined in different classes of the same hierarchy.
       */

      def areBothNonMethodic: Boolean =
        /* dotc fully compares signatures instead of doing this, which in theory
         * allows methodic term refs to be subtypes. We validated in
         *   https://github.com/lampepfl/dotty/pull/18045
         * that it breaks nothing to restrict subtyping to non-methodic term refs.
         */
        def isTermRefMethodic(tp: NamedType) = tp.asTermRef.underlyingOrMethodic.isInstanceOf[MethodicType]
        tp1.isType || (!isTermRefMethodic(tp1) && !isTermRefMethodic(tp2))

      def areBothClasses: Boolean =
        tp1.isType && tp1.asTypeRef.isClass && tp2.asTypeRef.isClass

      val trueBecauseOverriddenMembers =
        tp1.name == tp2.name
          && isSubPrefix(tp1.prefix, tp2.prefix)
          && areBothNonMethodic
          && !areBothClasses // classes can shadow each other without being subtypes

      trueBecauseOverriddenMembers || level2(tp1, tp2)
  end level1NamedNamed

  private def level2(tp1: Type, tp2: Type)(using Context): Boolean = tp1 match
    case tp1: NothingType =>
      true

    case tp1: TypeRef =>
      tp1.optAliasedType match
        case Some(alias) =>
          isSubType(alias, tp2)
            || level3(tp1, tp2)
        case _ =>
          level3(tp1, tp2)
      end match

    case tp1: ThisType =>
      val cls1 = tp1.cls
      tp2 match {
        case tp2: TermRef if cls1.isModuleClass && isTypeRefOf(tp2.underlying, cls1) =>
          (cls1.isStatic || isSubPrefix(cls1.localRef.prefix, tp2.prefix))
            || level3(tp1, tp2)
        case _ =>
          level3(tp1, tp2)
      }

    case tp1: OrType =>
      isSubType(tp1.first, tp2) && isSubType(tp1.second, tp2)

    case tp1: AnnotatedType =>
      isSubType(tp1.typ, tp2)

    case tp1: MatchType =>
      tp1.reduced match
        case Some(reduced) => isSubType(reduced, tp2)
        case None          => level3(tp1, tp2)

    case _ =>
      level3(tp1, tp2)
  end level2

  private def level3(tp1: Type, tp2: Type)(using Context): Boolean = tp2 match
    case TypeRef.OfClass(cls2) =>
      val tparams2 = cls2.typeParams
      if tparams2.isEmpty then
        if tp1.isLambdaSub then false // should be tp1.hasHigherKind, but the scalalib does not like that
        else if cls2.isAny then true
        else if cls2.isSingleton && isSingleton(tp1) then true
        else level3WithBaseType(tp1, tp2, cls2)
      else if tp1.isLambdaSub then isSubType(tp1, etaExpand(tp2, tparams2))
      else level4(tp1, tp2)

    case tp2: TypeRef =>
      isSubType(tp1, tp2.bounds.low)
        || level4(tp1, tp2)

    case tp2: TypeParamRef =>
      isSubType(tp1, tp2.bounds.low)
        || level4(tp1, tp2)

    case tp2: AppliedType =>
      compareAppliedType2(tp1, tp2)

    case tp2: TypeLambda =>
      tp1 match
        case tp1: TypeLambda =>
          // TODO Check bounds and variances
          tp1.paramRefs.lengthCompare(tp2.paramRefs) == 0
            && isSubType(tp1.resultType, tp2.appliedTo(tp1.paramRefs))
        case _ =>
          // Try eta-expansion
          val tparams1 = tp1.typeParams
          val etaExpandSuccess = tparams1.nonEmpty && isSubType(etaExpand(tp1, tparams1), tp2)
          etaExpandSuccess || level4(tp1, tp2)

    case tp2: RefinedType =>
      (isSubType(tp1, tp2.parent) && hasMatchingRefinedMember(tp1, tp2))
        || level4(tp1, tp2)

    case tp2: RecType =>
      tp1.dealias match
        case tp1: RecType =>
          isSubType(tp1.parent, tp2.expand(tp1.recThis))
        case tp1 =>
          val tp1stable = ensureStableSingleton(tp1)
          isSubType(fixRecs(tp1stable, tp1stable), tp2.expand(tp1stable))

    case tp2: OrType =>
      isSubType(tp1, tp2.first) || isSubType(tp1, tp2.second)
        || level4(tp1, tp2)

    case tp2: FlexibleType =>
      isSubType(tp1, tp2.nullableType)

    case tp2: ByNameType =>
      tp1 match
        case tp1: ByNameType => isSubType(tp1.resultType, tp2.resultType)
        case _               => level4(tp1, tp2)

    case tp2: RepeatedType =>
      tp1 match
        case tp1: RepeatedType => isSubType(tp1.elemType, tp2.elemType)
        case _                 => level4(tp1, tp2)

    case tp2: MatchType =>
      tp2.reduced match
        case Some(reduced) => isSubType(tp1, reduced)
        case None          => level4(tp1, tp2)

    case _ =>
      level4(tp1, tp2)
  end level3

  private def level3WithBaseType(tp1: Type, tp2: Type, cls2: ClassSymbol)(using Context): Boolean =
    nonExprBaseType(tp1, cls2) match
      case Some(base) if base ne tp1 => isSubType(tryCaptureConversion(tp1, base), tp2)
      case _                         => level4(tp1, tp2)
  end level3WithBaseType

  private def nonExprBaseType(tp1: Type, cls2: ClassSymbol)(using Context): Option[Type] =
    if tp1.isInstanceOf[ByNameType] then None
    else tp1.baseType(cls2)

  private def tryCaptureConversion(tp1: Type, base: Type)(using Context): Type =
    tp1 match
      case tp1: SingletonType =>
        base match
          case base: AppliedType if base.args.exists(_.isInstanceOf[WildcardTypeArg]) =>
            base.tycon match
              case tycon @ TypeRef.OfClass(cls) =>
                val typeParams = cls.typeParams
                val newArgs = base.args.lazyZip(typeParams).map { (arg, tparam) =>
                  arg match
                    case arg: WildcardTypeArg => TypeRef(tp1, tparam)
                    case _                    => arg
                }
                AppliedType(tycon, newArgs)
              case _ =>
                base
          case _ =>
            base
      case _ =>
        base
  end tryCaptureConversion

  private def compareAppliedType2(tp1: Type, tp2: AppliedType)(using Context): Boolean =
    // !!! There is similar code in TypeMatching.tryMatchPattern

    val tycon2 = tp2.tycon
    val tparams = tycon2.typeParams
    if tparams.isEmpty then
      throw InvalidProgramStructureException(s"found type constructor $tycon2 without type params in AppliedType")

    def isMatchingApply(tp1: Type): Boolean = tp1 match
      case tp1Applied: AppliedType =>
        tp1Applied.tycon match
          case tycon1: TypeRef =>
            tp2.tycon match
              case tycon2: TypeRef =>
                val tycon1Sym = tycon1.optSymbol
                val tycon2Sym = tycon2.optSymbol
                if tycon1Sym.isDefined && tycon1Sym == tycon2Sym && isSubPrefix(tycon1.prefix, tycon2.prefix) then
                  isSubArgs(tp1, tp1Applied.args, tp2.args, tparams)
                else false
              case _ =>
                false

          case tycon1: TypeParamRef =>
            tycon1 == tycon2 && isSubArgs(tp1, tp1Applied.args, tp2.args, tparams)

          case _ =>
            false
        end match

      case _ =>
        false
    end isMatchingApply

    tp2.tycon match
      case tycon2: TypeRef =>
        if isMatchingApply(tp1) then true
        else
          tycon2.optSymbol match
            case Some(cls2: ClassSymbol) =>
              (cls2.isTupleNClass && defn.hasGenericTuples && isSubType(tp1, defn.GenericTupleTypeOf(tp2.args)))
                || level3WithBaseType(tp1, tp2, cls2)
            case Some(sym2: TypeMemberSymbol) if sym2.isTypeAlias =>
              isSubType(tp1, tp2.superType)
            case _ =>
              // TODO? Handle bounded type lambdas (compareLower in TypeComparer)
              level4(tp1, tp2)
        end if

      case tycon2: TypeParamRef =>
        // TODO Compare with the lower bound of tycon2 (compareLower in TypeComparer)
        isMatchingApply(tp1)

      case _ =>
        val dealiased = tp2.dealias
        if dealiased ne tp2 then isSubType(tp1, dealiased)
        else false
  end compareAppliedType2

  private def isSubArgs(
    tp1: Type,
    args1: List[TypeOrWildcard],
    args2: List[TypeOrWildcard],
    tparams: List[TypeConstructorParam]
  )(using Context): Boolean =
    if args1.sizeCompare(args2) != 0 || args2.sizeCompare(tparams) != 0 then
      throw InvalidProgramStructureException(s"argument count mismatch: isSubArgs($args1, $args2, $tparams)")

    args1.lazyZip(args2).lazyZip(tparams).forall { (arg1, arg2, tparam) =>
      isSubTypeArg(arg1, arg2, tparam.variance.sign)
    }
  end isSubArgs

  private def etaExpand(tp: Type, tparams: List[TypeConstructorParam])(using Context): TypeLambda =
    TypeLambda.fromParamInfos(tparams)(tl => tp.appliedTo(tl.paramRefs))

  private def hasMatchingRefinedMember(tp1: Type, tp2: RefinedType)(using Context): Boolean =
    tp2 match
      case tp2: TypeRefinement =>
        tp1.resolveMember(tp2.refinedName, tp1) match
          case ResolveMemberResult.NotFound =>
            false
          case ResolveMemberResult.ClassMember(cls) =>
            tp2.refinedBounds.contains(tp1.select(cls))
          case ResolveMemberResult.TypeMember(symbols, bounds) =>
            tp2.refinedBounds.contains(bounds)
          case ResolveMemberResult.TermMember(symbols, tpe, isStable) =>
            throw AssertionError(s"found term member for $tp2 in $tp1")

      case tp2: TermRefinement =>
        if !tp2.isMethodic then
          tp1.resolveMember(tp2.refinedName, tp1) match
            case ResolveMemberResult.NotFound =>
              false
            case ResolveMemberResult.TermMember(_, tpe, isStable) =>
              tpe.isSubTypeOrMethodic(tp2.refinedType) && (isStable || !tp2.isStable)
            case _: ResolveMemberResult.ClassMember | _: ResolveMemberResult.TypeMember =>
              throw AssertionError(s"found type member for $tp2 in $tp1")
        else
          tp1.resolveMatchingMember(tp2.signedName, tp1, _.isSubTypeOrMethodic(tp2.refinedType)) match
            case ResolveMemberResult.NotFound =>
              false
            case _: ResolveMemberResult.TermMember =>
              true
            case _: ResolveMemberResult.ClassMember | _: ResolveMemberResult.TypeMember =>
              throw AssertionError(s"found type member for $tp2 in $tp1")
  end hasMatchingRefinedMember

  private def ensureStableSingleton(tp: Type)(using Context): SingletonType = tp match
    case tp: SingletonType if tp.isStable => tp
    case _                                => SkolemType(tp)

  /** Replace any top-level recursive type `{ z => T }` in `tp` with `[z := anchor]T`. */
  private def fixRecs(anchor: SingletonType, tp: Type)(using Context): Type =
    def fix(tp: Type): Type = tp match
      case tp: TypeProxy =>
        tp match
          case tp: RecType =>
            Substituters.substRecThis(fix(tp.parent), tp, anchor)
          case tp: TermRefinement =>
            tp.derivedTermRefinement(fix(tp.parent), tp.refinedName, tp.refinedType)
          case tp: TypeRefinement =>
            tp.derivedTypeRefinement(fix(tp.parent), tp.refinedName, tp.refinedBounds)
          case tp: TypeParamRef =>
            fixOrElse(tp.bounds.high, tp)
          case tp: TypeRef if tp.isClass =>
            tp
          case _ =>
            fixOrElse(tp.superType, tp)
      case tp: AndType =>
        tp.derivedAndType(fix(tp.first), fix(tp.second))
      case tp: OrType =>
        tp.derivedOrType(fix(tp.first), fix(tp.second))
      case tp =>
        tp
    end fix

    def fixOrElse(tp: Type, fallback: Type): Type =
      val tp1 = fix(tp)
      if tp1 ne tp then tp1 else fallback
    end fixOrElse

    fix(tp)
  end fixRecs

  private def level4(tp1: Type, tp2: Type)(using Context): Boolean = tp1 match
    case TypeRef.OfClass(cls1) =>
      if cls1.isNull then isNullable(tp2)
      else false

    case tp1: TypeRef =>
      isSubType(tp1.bounds.high, tp2)

    case tp1: TypeParamRef =>
      isSubType(tp1.bounds.high, tp2)

    case tp1: AppliedType =>
      compareAppliedType1(tp1, tp2)

    case tp1: SingletonType =>
      def comparePaths: Boolean =
        tp2 match
          case tp2: TermRef =>
            tp2.underlying.dealias match
              case tp2Singleton: SingletonType =>
                isSubType(tp1, tp2Singleton)
              case _ =>
                false
          case _ =>
            false

      def proceedWithWidenedType: Boolean =
        isSubType(tp1.underlying, tp2)

      comparePaths || proceedWithWidenedType

    case tp1: TypeLambda =>
      tp2 match
        case tp2: TypeLambda =>
          false // this case is already handled in level3
        case _ =>
          tp2.typeParams.lengthCompare(tp1.paramRefs) == 0
            && isSubType(tp1.resultType, tp2.appliedTo(tp1.paramRefs))

    case tp1: RefinedType =>
      isSubType(tp1.parent, tp2)

    case tp1: RecType =>
      isSubType(tp1.parent, tp2)

    case tp1: FlexibleType =>
      isSubType(tp1.nonNullableType, tp2)

    case tp1: AndType =>
      // TODO Try and simplify first
      isSubType(tp1.first, tp2) || isSubType(tp1.second, tp2)

    case tp1: RepeatedType =>
      isSubType(tp1.underlying, tp2)

    case tp1: MatchType =>
      def isSubMatchType: Boolean = tp2 match
        case tp2: MatchType =>
          isSameType(tp1.scrutinee, tp2.scrutinee) && tp1.cases.corresponds(tp2.cases)(isSubMatchTypeCase)
        case _ =>
          false

      isSubType(tp1.underlying, tp2) || isSubMatchType

    case _ =>
      false
  end level4

  private def compareAppliedType1(tp1: AppliedType, tp2: Type)(using Context): Boolean =
    val tycon1 = tp1.tycon
    tycon1 match
      case TypeRef.OfClass(_) =>
        false
      case tycon1: TypeProxy =>
        isSubType(tp1.superType, tp2) // TODO superTypeNormalized for match types
      case _ =>
        false
  end compareAppliedType1

  private def isSubMatchTypeCase(caze1: MatchTypeCase, caze2: MatchTypeCase)(using Context): Boolean =
    caze1.paramNames.lengthCompare(caze2.paramNames) == 0
      && isSameType(caze1.pattern, Substituters.substBinders(caze2.pattern, caze2, caze1))
      && isSubType(caze1.result, Substituters.substBinders(caze2.result, caze2, caze1))
  end isSubMatchTypeCase

  private def isSingleton(tp: Type)(using Context): Boolean = tp match
    case tp: SingletonType => tp.isStable
    case _                 => false
  end isSingleton

  private def isNullable(tp: Type)(using Context): Boolean = tp match
    case TypeRef.OfClass(cls) =>
      !cls.isValueClass && !cls.isModuleClass && !cls.isSingleton
    case tp: TypeRef =>
      false
    case tp: TermRef =>
      // Weird spec thing: x.type represents {x, null} when the underlying type of x is nullable :(
      tp.underlyingOrMethodic match
        case underlying: Type => isNullable(underlying)
        case _: MethodicType  => false
    case tp: AppliedType =>
      isNullable(tp.tycon)
    case tp: RefinedType =>
      isNullable(tp.parent)
    case tp: RecType =>
      isNullable(tp.parent)
    case tp: AndType =>
      isNullable(tp.first) && isNullable(tp.second)
    case tp: OrType =>
      isNullable(tp.first) || isNullable(tp.second)
    case tp: AnnotatedType =>
      isNullable(tp.typ)
    case _ =>
      false
  end isNullable

  private[tastyquery] def isSubPrefix(pre1: Prefix, pre2: Prefix)(using Context): Boolean =
    pre1 match
      case NoPrefix =>
        pre2 eq NoPrefix
      case pre1: PackageRef =>
        pre2 match
          case pre2: PackageRef   => pre1.symbol == pre2.symbol
          case NoPrefix | _: Type => false
      case pre1: Type =>
        pre2 match
          case pre2: Type               => isSubType(pre1, pre2)
          case NoPrefix | _: PackageRef => false
  end isSubPrefix

  private def isTypeRefOf(tp: TypeOrMethodic, cls: ClassSymbol)(using Context): Boolean = tp match
    case tp: TypeRef => tp.isSpecificClass(cls)
    case _           => false
end Subtyping
