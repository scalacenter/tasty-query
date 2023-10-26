package tastyquery

import scala.annotation.tailrec

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Modifiers.*
import tastyquery.Names.termName
import tastyquery.Symbols.*
import tastyquery.Types.*
import tastyquery.TypeMaps.*
import tastyquery.Subtyping.{isSameType, isSubType}

private[tastyquery] object TypeMatching:
  private enum MatchResult:
    case Reduced(tp: Type)
    case Disjoint
    case Stuck

  def matchCases(scrutinee: Type, cases: List[MatchTypeCase])(using Context): Option[Type] =
    /* Spec: If the scrutinee type S is an empty set of values (such as
     * `Nothing` or `String & Int`), do not reduce.
     */
    if provablyEmpty(scrutinee) then None
    else
      /* Spec: Sequentially consider each pattern Pi
       *
       * - If S <: Pi reduce to Ti.
       * - Otherwise, try constructing a proof that S and Pi are disjoint, or,
       *   in other words, that no value s of type S is also of type Pi.
       *   If such a proof is found, proceed to the next case (Pi+1).
       * - Otherwise, do not reduce.
       */
      @tailrec
      def loop(cases: List[MatchTypeCase]): Option[Type] = cases match
        case caze :: casesRest =>
          matchCase(scrutinee, caze) match
            case MatchResult.Reduced(result) =>
              Some(result)
            case MatchResult.Disjoint =>
              loop(casesRest)
            case MatchResult.Stuck =>
              None
        case Nil =>
          None
      end loop

      loop(cases)
  end matchCases

  private def matchCase(scrutinee: Type, caze: MatchTypeCase)(using Context): MatchResult =
    if caze.paramNames.isEmpty then
      // fast path
      if scrutinee.isSubType(caze.pattern) then MatchResult.Reduced(caze.result)
      else if provablyDisjoint(scrutinee, caze.pattern) then MatchResult.Disjoint
      else MatchResult.Stuck
    else
      val typeParamInstantiations = new Array[Type | Null](caze.paramNames.size)
      if tryMatchPattern(scrutinee, caze.pattern, Variance.Covariant, caze, typeParamInstantiations) then
        val actualTypeParams = typeParamInstantiations.toList.map(_.nn)
        val reduced = Substituters.substParams(caze.result, caze, actualTypeParams)
        MatchResult.Reduced(reduced)
      else if provablyDisjoint(scrutinee, caze.pattern) then MatchResult.Disjoint
      else MatchResult.Stuck
  end matchCase

  private def containsCapturesOf(pattern: TypeOrWildcard, caze: MatchTypeCase)(using Context): Boolean =
    pattern match
      case pattern: TypeParamRef =>
        pattern.binder eq caze
      case pattern: AppliedType =>
        pattern.args.exists(containsCapturesOf(_, caze))
      case _ =>
        false
  end containsCapturesOf

  private def tryMatchPattern(
    scrutinee: TypeOrWildcard,
    pattern: TypeOrWildcard,
    variance: Variance,
    caze: MatchTypeCase,
    typeParamInstantiations: Array[Type | Null]
  )(using Context): Boolean =
    pattern match
      case pattern: TypeParamRef if pattern.binder eq caze =>
        val instantiation = scrutinee match
          case scrutinee: WildcardTypeArg =>
            val bounds = scrutinee.bounds
            variance match
              case Variance.Covariant     => Some(bounds.high)
              case Variance.Contravariant => Some(bounds.low)
              case Variance.Invariant =>
                if bounds.low.isSameType(bounds.high) then Some(bounds.low)
                else None
          case scrutinee: Type =>
            Some(scrutinee)

        instantiation match
          case Some(result) =>
            typeParamInstantiations(pattern.paramNum) = result
            true
          case None =>
            false

      case pattern: AppliedType if containsCapturesOf(pattern, caze) =>
        // !!! There is similar code in Subtyping.compareAppliedType2

        def tryMatchArgs(
          scrutineeArgs: List[TypeOrWildcard],
          patternArgs: List[TypeOrWildcard],
          tparams: List[TypeConstructorParam]
        ): Boolean =
          assert(
            scrutineeArgs.isEmpty == patternArgs.isEmpty && scrutineeArgs.isEmpty == tparams.isEmpty,
            s"tryMatchArgs($scrutineeArgs, $patternArgs, $tparams)"
          )
          if scrutineeArgs.isEmpty then true
          else
            val innerVariance = tparams.head.variance * variance
            tryMatchPattern(scrutineeArgs.head, patternArgs.head, innerVariance, caze, typeParamInstantiations)
            && tryMatchArgs(scrutineeArgs.tail, patternArgs.tail, tparams.tail)
        end tryMatchArgs

        def tryMatchingApply(patternTycon: TypeRef): Boolean = scrutinee.highIfWildcard match
          case scrutinee: AppliedType =>
            scrutinee.tycon match
              case scrutineeTycon: TypeRef =>
                val scrutineeTyconSym = scrutineeTycon.optSymbol
                val patternTyconSym = patternTycon.optSymbol
                val sameTycon = scrutineeTyconSym.isDefined && scrutineeTyconSym == patternTyconSym
                if sameTycon && Subtyping.isSubPrefix(scrutineeTycon.prefix, patternTycon.prefix) then
                  tryMatchArgs(scrutinee.args, pattern.args, patternTycon.typeParams)
                else false

              case _ =>
                false
            end match

          case _ =>
            false
        end tryMatchingApply

        pattern.tycon match
          case _ if variance == Variance.Contravariant =>
            /* See https://github.com/lampepfl/dotty/issues/17121
             * dotc does the wrong thing in this case, and it is not clear that
             * there *exists* a correct solution, so we always bail.
             */
            false

          case _ if variance == Variance.Invariant && scrutinee.isInstanceOf[WildcardTypeArg] =>
            false

          case patternTycon: TypeRef =>
            if tryMatchingApply(patternTycon) then true
            else
              patternTycon.optSymbol match
                case Some(patternCls: ClassSymbol) =>
                  scrutinee.highIfWildcard.baseType(patternCls) match
                    case Some(scrutineeBase) if scrutineeBase ne scrutinee =>
                      tryMatchPattern(scrutineeBase, pattern, variance, caze, typeParamInstantiations)
                    case _ =>
                      false
                case Some(patternTyconSym: TypeMemberSymbol) if patternTyconSym.isTypeAlias =>
                  tryMatchPattern(scrutinee, pattern.superType, variance, caze, typeParamInstantiations)
                case _ =>
                  false
            end if

          case _ =>
            false

      case _ =>
        Subtyping.isSubTypeArg(scrutinee, pattern, variance.sign)
  end tryMatchPattern

  /** Is `tp` a provably empty type?
    *
    * `true` implies that we found a proof; uncertainty defaults to `false`.
    */
  private def provablyEmpty(tp: Type)(using Context): Boolean =
    tp.dealias match
      case tp if tp.isExactlyNothing =>
        true
      case tp: AndType =>
        provablyDisjoint(tp.first, tp.second)
      case tp: OrType =>
        provablyEmpty(tp.first) && provablyEmpty(tp.second)
      case tp: AppliedType =>
        tp.args.lazyZip(tp.tycon.typeParams).exists { (arg, tparam) =>
          tparam.variance.sign >= 0
          && provablyEmpty(arg.highIfWildcard)
          && typeparamCorrespondsToField(tp.tycon, tparam)
        }
      case TypeRef.OfClass(_) =>
        false
      case tp: TypeProxy =>
        provablyEmpty(tp.underlying)
      case _ =>
        false
  end provablyEmpty

  /** Are `tp1` and `tp2` provably disjoint types?
    *
    * `true` implies that we found a proof; uncertainty defaults to `false`.
    *
    * Proofs rely on the following properties of Scala types:
    *
    * 1. Single inheritance of classes
    * 2. Final classes cannot be extended
    * 3. ConstantTypes with distinct values are non intersecting
    * 4. TermRefs with distinct values are non intersecting
    * 5. There is no value of type Nothing
    *
    * Note on soundness: the correctness of match types relies on on the
    * property that in all possible contexts, the same match type expression
    * is either stuck or reduces to the same case.
    */
  private def provablyDisjoint(tp1: Type, tp2: Type)(using Context): Boolean =
    def isEnumValue(ref: TermRef): Boolean =
      ref.symbol.isEnumCase // TODO? Exclude Java enums here?

    def isEnumValueOrModule(ref: TermRef): Boolean =
      isEnumValue(ref) || ref.symbol.isModuleVal || (ref.underlying match {
        case tp: TermRef => isEnumValueOrModule(tp)
        case _           => false
      })

    (tp1.dealias, tp2.dealias) match
      case _ if tp1.isFromJavaObject =>
        provablyDisjoint(defn.AnyType, tp2)
      case _ if tp2.isFromJavaObject =>
        provablyDisjoint(tp1, defn.AnyType)

      case (tp1: ConstantType, tp2: ConstantType) =>
        // Property 3
        tp1.value != tp2.value

      case (TypeRef.OfClass(cls1), TypeRef.OfClass(cls2)) =>
        if cls1.isSubClass(cls2) || cls2.isSubClass(cls1) then
          // One of them is a subclass of the other -> not disjoint
          false
        else if cls1.openLevel == OpenLevel.Final || cls2.openLevel == OpenLevel.Final then
          // One of them is final and they are unrelated -> disjoint (property 2)
          true
        else if !cls1.isTrait && !cls2.isTrait then
          // They are both non-trait classes and unrelated -> disjoint (property 1)
          true
        else
          // TODO Decompose sealed classes
          false

      case (tp1: AppliedType, tp2: AppliedType) if isSameType(tp1.tycon, tp2.tycon) =>
        val tycon1 = tp1.tycon

        /* It is possible to conclude that two types applies are disjoint by
         * looking at covariant type parameters if the said type parameters
         * are disjoin and correspond to fields.
         * (Type parameter disjointness is not enough by itself as it could
         * lead to incorrect conclusions for phantom type parameters).
         */
        def covariantDisjoint(tp1: TypeOrWildcard, tp2: TypeOrWildcard, tparam: TypeConstructorParam): Boolean =
          provablyDisjoint(tp1.highIfWildcard, tp2.highIfWildcard) && typeparamCorrespondsToField(tycon1, tparam)

        /* Contravariant case: a value where this type parameter is
         * instantiated to `Any` belongs to both types.
         */
        def contravariantDisjoint(tp1: TypeOrWildcard, tp2: TypeOrWildcard, tparam: TypeConstructorParam): Boolean =
          false

        /* In the invariant case, we also use a stronger notion of disjointness:
         * we consider fully instantiated types not equal wrt =:= to be disjoint
         * (under any context). This is fine because it matches the runtime
         * semantics of pattern matching. To implement a pattern such as
         * `case Inv[T] => ...`, one needs a type tag for `T` and the compiler
         * is used at runtime to check it the scrutinee's type is =:= to `T`.
         * Note that this is currently a theoretical concern since Dotty
         * doesn't have type tags, meaning that users cannot write patterns
         * that do type tests on higher kinded types.
         */
        def invariantDisjoint(tp1: TypeOrWildcard, tp2: TypeOrWildcard, tparam: TypeConstructorParam): Boolean =
          provablyDisjoint(tp1.highIfWildcard, tp2.highIfWildcard) /*||
          !isSameType(tp1, tp2) &&
          fullyInstantiated(tp1) && // We can only trust a "no" from `isSameType` when
          fullyInstantiated(tp2)    // both `tp1` and `tp2` are fully instantiated.*/

        tp1.args.lazyZip(tp2.args).lazyZip(tycon1.typeParams).exists { (arg1, arg2, tparam) =>
          tparam.variance match
            case Variance.Covariant     => covariantDisjoint(arg1, arg2, tparam)
            case Variance.Contravariant => contravariantDisjoint(arg1, arg2, tparam)
            case Variance.Invariant     => invariantDisjoint(arg1, arg2, tparam)
        }

      case (tp1: TermRef, tp2: TermRef) if isEnumValueOrModule(tp1) && isEnumValueOrModule(tp2) =>
        tp1.symbol != tp2.symbol
      case (tp1: TermRef, tp2: TypeRef) if isEnumValue(tp1) =>
        !tp1.isSubType(tp2)
      case (tp1: TypeRef, tp2: TermRef) if isEnumValue(tp2) =>
        !tp2.isSubType(tp1)

      case (tp1: TypeProxy, tp2: TypeProxy) =>
        def trySuperTp1 = tp1 match
          case TypeRef.OfClass(_) => false
          case _                  => provablyDisjoint(tp1.superTypeNormalized, tp2)
        def trySuperTp2 = tp2 match
          case TypeRef.OfClass(_) => false
          case _                  => provablyDisjoint(tp1, tp2.superTypeNormalized)
        trySuperTp1 || trySuperTp2
      case (tp1: TypeProxy, _) =>
        provablyDisjoint(tp1.superTypeNormalized, tp2)
      case (_, tp2: TypeProxy) =>
        provablyDisjoint(tp1, tp2.superTypeNormalized)

      case _ =>
        false
  end provablyDisjoint

  /** Does `tycon` have a field with type `tparam`? */
  private def typeparamCorrespondsToField(tycon: Type, tparam: TypeConstructorParam)(using Context): Boolean =
    productSelectorTypes(tycon).exists {
      case tp: TypeRef => tp.isTypeParamRef(tparam)
      case tp          => false
    } /*|| tycon.derivesFrom(defn.PairClass)*/
  end typeparamCorrespondsToField

  private def productSelectorTypes(tycon: Type)(using Context): Iterator[Type] =
    Iterator
      .from(1)
      .map { index =>
        tycon.resolveMember(termName("_" + index), tycon) match
          case ResolveMemberResult.TermMember(_, declaredType: Type, _) => Some(declaredType)
          case _                                                        => None
      }
      .takeWhile(_.isDefined)
      .map(_.get)
end TypeMatching
