package tastyquery

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Symbols.*
import tastyquery.Types.*
import tastyquery.TypeMaps.*

private[tastyquery] object Subtyping:
  def isSameType(tp1: Type, tp2: Type)(using Context): Boolean =
    isSubtype(tp1, tp2) && isSubtype(tp2, tp1)

  def isSubtype(tp1: Type, tp2: Type)(using Context): Boolean =
    // `eq` is semantically important for identity-based types such as `TypeParamRef`
    (tp1 eq tp2) || level1(tp1, tp2)

  private def level1(tp1: Type, tp2: Type)(using Context): Boolean = tp2 match
    case tp2: NamedType =>
      // Try follow type alias
      val sym2 = tp2.symbol
      sym2 match
        case sym2: TypeMemberSymbol if sym2.isTypeAlias =>
          if isSubtype(tp1, sym2.aliasedTypeAsSeenFrom(tp2.prefix)) then return true
        case _ =>
          ()
      end match

      tp1 match
        case tp1: NamedType =>
          val sym1 = tp1.symbol
          sym1 match
            case sym1: TypeMemberSymbol if sym1.isTypeAlias =>
              if isSubtype(sym1.aliasedTypeAsSeenFrom(tp1.prefix), tp2) then return true
            case _ =>
              ()
          end match
          level1NamedNamed(tp1, tp2)

        case _ =>
          level2(tp1, tp2)

    case tp2: WildcardTypeBounds =>
      isSubtype(tp1, tp2.bounds.high)

    case tp2: ThisType =>
      val cls2 = tp2.cls
      tp1 match
        case tp1: ThisType =>
          tp1.cls == cls2
        case tp1: NamedType if cls2.is(Module) && cls2 == tp1.symbol =>
          (cls2.isStatic || isSubprefix(tp1.prefix, cls2.typeRef.prefix))
            || level2(tp1, tp2)
        case _ =>
          level2(tp1, tp2)

    case tp2: AndType =>
      isSubtype(tp1, tp2.first) && isSubtype(tp1, tp2.second)

    case tp2: ConstantType =>
      tp1 match
        case tp1: ConstantType =>
          tp1.value == tp2.value
        case _ =>
          level2(tp1, tp2)

    case tp2: AnnotatedType =>
      isSubtype(tp1, tp2.typ)

    case _ =>
      level2(tp1, tp2)
  end level1

  private def level1NamedNamed(tp1: NamedType, tp2: NamedType)(using Context): Boolean =
    val sym1 = tp1.symbol
    val sym2 = tp2.symbol

    if sym1 == sym2 then
      sym1.isStatic
      || isSubprefix(tp1.prefix, tp2.prefix)
      || level2(tp1, tp2)
    else
      /* When the symbols are not the same, we could still have a subtyping
       * relationship if they are defined in different classes of the same hierarchy.
       */
      val trueBecauseOverriddenMembers =
        sym1.name == sym2.name
          && isSubprefix(tp1.prefix, tp2.prefix)
          && tp1.optSignature == tp2.optSignature
          && !(sym1.isClass && sym2.isClass) // classes can shadow each other without being subtypes
      trueBecauseOverriddenMembers || level2(tp1, tp2)
  end level1NamedNamed

  private def level2(tp1: Type, tp2: Type)(using Context): Boolean = tp1 match
    case tp1: NamedType =>
      val sym1 = tp1.symbol
      sym1 match
        case sym1: TypeMemberSymbol if sym1.isTypeAlias =>
          if isSubtype(sym1.aliasedTypeAsSeenFrom(tp1.prefix), tp2) then true
          else level3(tp1, tp2)
        case _ =>
          (sym1 == defn.NothingClass || isBottom(tp1))
            || level3(tp1, tp2)
      end match

    case tp1: ThisType =>
      val cls1 = tp1.cls
      tp2 match {
        case tp2: TermRef if cls1.is(Module) && tp2.symbol.declaredType.isRef(cls1) =>
          (cls1.isStatic || isSubprefix(cls1.typeRef.prefix, tp2.prefix))
            || level3(tp1, tp2)
        case _ =>
          level3(tp1, tp2)
      }

    case tp1: WildcardTypeBounds =>
      isSubtype(tp1.bounds.low, tp2)

    case tp1: OrType =>
      isSubtype(tp1.first, tp2) && isSubtype(tp1.second, tp2)

    case tp1: AnnotatedType =>
      isSubtype(tp1.typ, tp2)

    case _ =>
      level3(tp1, tp2)
  end level2

  private def level3(tp1: Type, tp2: Type)(using Context): Boolean = tp2 match
    case tp2: TypeRef =>
      tp2.symbol match
        case cls2: ClassSymbol =>
          if cls2.typeParams.isEmpty then
            if cls2 == defn.AnyKindClass then true
            else if isBottom(tp1) then true
            else if tp1.isLambdaSub then false // should be tp1.hasHigherKind, but the scalalib does not like that
            else if cls2 == defn.AnyClass then true
            else level3WithBaseType(tp1, tp2, cls2)
          else
            // TODO Try eta-expansion if tp1.isLambdaSub && !tp1.isAnyKind
            level4(tp1, tp2)
        case sym2: TypeSymbolWithBounds =>
          isSubtype(tp1, tp2.prefix.memberTypeBoundsLow(sym2))
            || level4(tp1, tp2)
      end match

    case tp2: AppliedType =>
      compareAppliedType2(tp1, tp2)

    case tp2: TypeLambda =>
      tp1 match
        case tp1: TypeLambda =>
          // TODO Check bounds and variances
          tp1.paramRefs.lengthCompare(tp2.paramRefs) == 0
            && isSubtype(tp1.resultType, tp2.appliedTo(tp1.paramRefs))
        case _ =>
          // TODO? Eta-expand polymorphic type constructors?
          level4(tp1, tp2)

    case tp2: OrType =>
      isSubtype(tp1, tp2.first) || isSubtype(tp1, tp2.second)
        || level4(tp1, tp2)

    case tp2: ByNameType =>
      tp1 match
        case tp1: ByNameType => isSubtype(tp1.resultType, tp2.resultType)
        case _               => level4(tp1, tp2)

    case _ =>
      level4(tp1, tp2)
  end level3

  private def level3WithBaseType(tp1: Type, tp2: Type, cls2: ClassSymbol)(using Context): Boolean =
    nonExprBaseType(tp1, cls2) match
      case Some(base) if base ne tp1 => isSubtype(base, tp2)
      case _                         => level4(tp1, tp2)
  end level3WithBaseType

  private def nonExprBaseType(tp1: Type, cls2: ClassSymbol)(using Context): Option[Type] =
    if tp1.isInstanceOf[ByNameType] then None
    else tp1.baseType(cls2)

  private def compareAppliedType2(tp1: Type, tp2: AppliedType)(using Context): Boolean =
    val tycon2 = tp2.tycon
    val tparams = tycon2.typeParams
    if tparams.isEmpty then
      throw InvalidProgramStructureException(s"found type constructor $tycon2 without type params in AppliedType")

    def isMatchingApply(tp1: Type): Boolean = tp1.widen match
      case tp1: AppliedType =>
        tp1.tycon match
          case tycon1: TypeRef =>
            tp2.tycon match
              case tycon2: TypeRef =>
                val tycon1Sym = tycon1.symbol
                val tycon2Sym = tycon2.symbol
                if tycon1Sym == tycon2Sym && isSubprefix(tycon1.prefix, tycon2.prefix) then
                  isSubArgs(tp1.args, tp2.args, tparams)
                else false
              case _ =>
                false

          case tycon1: TypeParamRef =>
            tycon1 == tycon2 && isSubArgs(tp1.args, tp2.args, tparams)

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
          tycon2.symbol match
            case cls2: ClassSymbol =>
              // TODO Handle generic tuple <: TupleN
              level3WithBaseType(tp1, tp2, cls2)
            case sym2: TypeMemberSymbol if sym2.isTypeAlias =>
              isSubtype(tp1, tp2.superType)
            case sym2: TypeSymbolWithBounds =>
              // TODO? Handle bounded type lambdas (compareLower in TypeComparer)
              level4(tp1, tp2)
        end if

      case tycon2: TypeParamRef =>
        // TODO Compare with the lower bound of tycon2 (compareLower in TypeComparer)
        isMatchingApply(tp1)

      case _ =>
        false
  end compareAppliedType2

  private def isSubArgs(args1: List[Type], args2: List[Type], tparams2: List[TypeParamInfo])(using Context): Boolean =
    def isSubArg(arg1: Type, arg2: Type, tparam2: TypeParamInfo): Boolean =
      val variance = tparam2.paramVariance

      arg2 match
        case arg2: WildcardTypeBounds =>
          arg2.bounds.contains(arg1)
        case _ =>
          arg1 match
            case arg1: WildcardTypeBounds =>
              // TODO? Capture conversion
              false
            case _ =>
              variance.sign match
                case 1  => isSubtype(arg1, arg2)
                case -1 => isSubtype(arg2, arg1)
                case 0  => isSameType(arg1, arg2)
    end isSubArg

    if args1.sizeCompare(args2) != 0 || args2.sizeCompare(tparams2) != 0 then
      throw InvalidProgramStructureException(s"argument count mismatch: isSubArgs($args1, $args2, $tparams2)")

    args1.lazyZip(args2).lazyZip(tparams2).forall { (arg1, arg2, tparam2) =>
      isSubArg(arg1, arg2, tparam2)
    }
  end isSubArgs

  private def level4(tp1: Type, tp2: Type)(using Context): Boolean = tp1 match
    case tp1: TypeRef =>
      tp1.symbol match
        case cls1: ClassSymbol =>
          if cls1 == defn.NothingClass then true
          else if cls1 == defn.NullClass then isNullable(tp2)
          else false

        case sym1: TypeSymbolWithBounds =>
          isSubtype(tp1.prefix.memberTypeBoundsHigh(sym1), tp2)
      end match

    case tp1: AppliedType =>
      compareAppliedType1(tp1, tp2)

    case tp1: SingletonType =>
      def comparePaths: Boolean =
        tp2 match
          case tp2: TermRef =>
            tp2.symbol.declaredTypeAsSeenFrom(tp2.prefix).dealias match
              case tp2Singleton: SingletonType =>
                isSubtype(tp1, tp2Singleton)
              case _ =>
                false
          case _ =>
            false

      def proceedWithWidenedType: Boolean =
        isSubtype(tp1.underlying, tp2)

      comparePaths || proceedWithWidenedType

    case tp1: TypeLambda =>
      tp2 match
        case tp2: TypeLambda =>
          false // this case is already handled in level3
        case _ =>
          tp2.typeParams.lengthCompare(tp1.paramRefs) == 0
            && isSubtype(tp1.resultType, tp2.appliedTo(tp1.paramRefs))

    case tp1: AndType =>
      // TODO Try and simplify first
      isSubtype(tp1.first, tp2) || isSubtype(tp1.second, tp2)

    case _ =>
      false
  end level4

  private def compareAppliedType1(tp1: AppliedType, tp2: Type)(using Context): Boolean =
    val tycon1 = tp1.tycon
    tycon1 match
      case tycon1: TypeRef if tycon1.symbol.isClass =>
        false
      case tycon1: TypeProxy =>
        isSubtype(tp1.superType, tp2) // TODO superTypeNormalized for match types
      case _ =>
        false
  end compareAppliedType1

  private def isNullable(tp: Type)(using Context): Boolean = tp match
    case tp: TypeRef =>
      tp.symbol match
        case cls: ClassSymbol =>
          !cls.isValueClass && !cls.is(Module) && cls != defn.NothingClass
        case _: TypeSymbolWithBounds =>
          false
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

  private def isSubprefix(pre1: Prefix, pre2: Prefix)(using Context): Boolean =
    pre1 match
      case NoPrefix =>
        pre2 eq NoPrefix
      case pre1: PackageRef =>
        // fast path for prefixes
        pre2 match
          case pre2: PackageRef => pre1.symbol == pre2.symbol
          case _                => false
      case pre1: Type =>
        pre2 match
          case pre2: Type => isSubtype(pre1, pre2)
          case NoPrefix   => false
  end isSubprefix

  private def isBottom(tp: Type)(using Context): Boolean =
    tp.widen.isRef(defn.NothingClass)
end Subtyping
