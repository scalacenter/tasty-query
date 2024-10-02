package tastyquery

import scala.annotation.tailrec

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Types.*
import tastyquery.Types.ErasedTypeRef.*

private[tastyquery] object Erasure:
  @deprecated("use the overload that takes an explicit SourceLanguage", since = "0.7.1")
  def erase(tpe: Type)(using Context): ErasedTypeRef =
    erase(tpe, SourceLanguage.Scala3)

  def erase(tpe: Type, language: SourceLanguage)(using Context): ErasedTypeRef =
    erase(tpe, language, keepUnit = false)

  def erase(tpe: Type, language: SourceLanguage, keepUnit: Boolean)(using Context): ErasedTypeRef =
    given SourceLanguage = language
    finishErase(preErase(tpe, keepUnit))
  end erase

  private[tastyquery] def eraseForSigName(tpe: Type, language: SourceLanguage, keepUnit: Boolean)(
    using Context
  ): ErasedTypeRef =
    given SourceLanguage = language

    val patchedPreErased = preErase(tpe, keepUnit) match
      case ArrayTypeRef(ClassRef(cls), dimensions) if cls.isDerivedValueClass =>
        // Hack! dotc's `sigName` does *not* correspond to erasure in this case!
        val patchedBase =
          if cls.typeParams.isEmpty then preEraseMonoValueClass(cls)
          else preErasePolyValueClass(cls, cls.typeParams.map(_.localRef))
        patchedBase.underlying.multiArrayOf(dimensions)
      case typeRef =>
        typeRef

    finishErase(patchedPreErased)
  end eraseForSigName

  /** The pre-erasure of a value class.
    *
    * It primarily represents the underlying erased type. However, it also
    * remembers the originating value class symbol. Different fields are used
    * in different contexts:
    *
    * - Normally, the `underlying` type is used.
    * - As the argument of `Array`s, the `valueClass` is used instead.
    * - In `erasedGlb`, the `valueClass` is used for the *ordering* criteria,
    *   but the `underlying` type is used for the actual erasure.
    */
  private final case class ErasedValueClass(valueClass: ClassSymbol, underlying: ErasedTypeRef)

  private type PreErasedTypeRef = ErasedTypeRef | ErasedValueClass

  /** First pass of erasure, where where value classes become `ErasedValueClass`es. */
  private def preErase(tpe: Type, keepUnit: Boolean)(using Context, SourceLanguage): PreErasedTypeRef =
    def arrayOf(tpe: TypeOrWildcard): ErasedTypeRef =
      if isGenericArrayElement(tpe) then defn.ObjectClass.erasure
      else
        preErase(tpe.highIfWildcard, keepUnit = false) match
          case base: ErasedTypeRef             => base.arrayOf()
          case ErasedValueClass(valueClass, _) => valueClass.erasure.arrayOf()

    tpe match
      case tpe: AppliedType =>
        tpe.tycon match
          case TypeRef.OfClass(cls) =>
            if cls.isArray then
              val List(targ) = tpe.args: @unchecked
              arrayOf(targ)
            else if cls.isDerivedValueClass then preErasePolyValueClass(cls, tpe.args)
            else cls.erasure
          case _ =>
            preErase(tpe.translucentSuperType, keepUnit)
      case TypeRef.OfClass(cls) =>
        if !keepUnit && cls.isUnit then defn.ErasedBoxedUnitClass.erasure
        else if cls.isDerivedValueClass then preEraseMonoValueClass(cls)
        else cls.erasure
      case tpe: TypeRef =>
        preErase(tpe.translucentSuperType, keepUnit)
      case tpe: SingletonType =>
        preErase(tpe.underlying, keepUnit)
      case tpe: TypeParamRef =>
        preErase(tpe.bounds.high, keepUnit)
      case tpe: MatchType =>
        tpe.reduced match
          case Some(reduced) => preErase(reduced, keepUnit)
          case None          => preErase(tpe.bound, keepUnit)
      case tpe: OrType =>
        erasedLub(
          finishErase(preErase(tpe.first, keepUnit = false)),
          finishErase(preErase(tpe.second, keepUnit = false))
        )
      case tpe: AndType =>
        summon[SourceLanguage] match
          case SourceLanguage.Java =>
            preErase(tpe.first, keepUnit = false)
          case SourceLanguage.Scala2 =>
            preErase(Scala2Erasure.eraseAndType(tpe), keepUnit = false)
          case SourceLanguage.Scala3 =>
            erasedGlb(preErase(tpe.first, keepUnit = false), preErase(tpe.second, keepUnit = false))
      case tpe: AnnotatedType =>
        preErase(tpe.typ, keepUnit)
      case tpe @ defn.PolyFunctionType(mt) =>
        defn.PolyFunctionType.functionClassOf(mt).erasure
      case tpe: RefinedType =>
        preErase(tpe.parent, keepUnit)
      case tpe: RecType =>
        preErase(tpe.parent, keepUnit)
      case tpe: FlexibleType =>
        preErase(tpe.nonNullableType, keepUnit)
      case _: ByNameType =>
        defn.Function0Class.erasure
      case tpe: RepeatedType =>
        if summon[SourceLanguage] == SourceLanguage.Java then arrayOf(tpe.elemType)
        else defn.SeqClass.erasure
      case _: NothingType =>
        defn.ErasedNothingClass.erasure
      case _: AnyKindType =>
        defn.ObjectClass.erasure
      case _: TypeLambda | _: CustomTransientGroundType =>
        throw IllegalArgumentException(s"Unexpected type in erasure: $tpe")
  end preErase

  private def finishErase(typeRef: PreErasedTypeRef)(using Context, SourceLanguage): ErasedTypeRef =
    typeRef match
      case typeRef: ErasedTypeRef          => typeRef
      case ErasedValueClass(_, underlying) => finishErase(underlying)
  end finishErase

  private def preEraseMonoValueClass(cls: ClassSymbol)(using Context, SourceLanguage): ErasedValueClass =
    val ctor = cls.findNonOverloadedDecl(nme.Constructor)

    val underlying = ctor.declaredType match
      case tpe: MethodType if tpe.paramNames.sizeIs == 1 =>
        tpe.paramTypes.head
      case _ =>
        throw InvalidProgramStructureException(s"Illegal value class constructor type ${ctor.declaredType.showBasic}")

    // The underlying of value classes are never value classes themselves (by language spec)
    val erasedUnderlying = preErase(underlying, keepUnit = false).asInstanceOf[ErasedTypeRef]

    ErasedValueClass(cls, erasedUnderlying)
  end preEraseMonoValueClass

  private def preErasePolyValueClass(cls: ClassSymbol, targs: List[TypeOrWildcard])(
    using Context,
    SourceLanguage
  ): ErasedValueClass =
    val ctor = cls.findNonOverloadedDecl(nme.Constructor)

    def illegalConstructorType(): Nothing =
      throw InvalidProgramStructureException(s"Illegal value class constructor type ${ctor.declaredType.showBasic}")

    def ctorParamType(tpe: TypeOrMethodic): Type = tpe match
      case tpe: MethodType if tpe.paramTypes.sizeIs == 1 => tpe.paramTypes.head
      case _                                             => illegalConstructorType()

    val ctorPolyType = ctor.declaredType match
      case tpe: PolyType => tpe
      case _             => illegalConstructorType()

    val genericUnderlying = ctorParamType(ctorPolyType.resultType)
    val specializedUnderlying = ctorParamType(ctorPolyType.instantiate(targs))

    // The underlying of value classes are never value classes themselves (by language spec)
    val erasedGenericUnderlying = preErase(genericUnderlying, keepUnit = false).asInstanceOf[ErasedTypeRef]
    val erasedSpecializedUnderlying = preErase(specializedUnderlying, keepUnit = false).asInstanceOf[ErasedTypeRef]

    def isPrimitive(typeRef: ErasedTypeRef): Boolean = typeRef match
      case ClassRef(cls)   => cls.isPrimitiveValueClass
      case _: ArrayTypeRef => false

    /* Ideally, we would just use `erasedSpecializedUnderlying` as the erasure of `tp`.
     * However, there are two special cases for polymorphic value classes, which
     * historically come from Scala 2:
     *
     * - Given `class Foo[A](x: A) extends AnyVal`, `Foo[X]` should erase like
     *   `X`, except if its a primitive in which case it erases to the boxed
     *   version of this primitive.
     * - Given `class Bar[A](x: Array[A]) extends AnyVal`, `Bar[X]` will be
     *   erased like `Array[A]` as seen from its definition site, no matter
     *   the `X` (same if `A` is bounded).
     */
    val erasedValueClass =
      if isPrimitive(erasedSpecializedUnderlying) && !isPrimitive(erasedGenericUnderlying) then
        erasedSpecializedUnderlying.asInstanceOf[ClassRef].cls.boxedClass.erasure
      else if genericUnderlying.baseType(defn.ArrayClass).isDefined then erasedGenericUnderlying
      else erasedSpecializedUnderlying

    ErasedValueClass(cls, erasedValueClass)
  end preErasePolyValueClass

  /** Is `Array[tp]` a generic Array that needs to be erased to `Object`?
    * This is true if among the subtypes of `Array[tp]` there is either:
    * - both a reference array type and a primitive array type
    *   (e.g. `Array[_ <: Int | String]`, `Array[_ <: Any]`)
    * - or two different primitive array types (e.g. `Array[_ <: Int | Double]`)
    * In both cases the erased lub of those array types on the JVM is `Object`.
    *
    * In addition, if `isScala2` is true, we mimic the Scala 2 erasure rules and
    * also return true for element types upper-bounded by a non-reference type
    * such as in `Array[_ <: Int]` or `Array[_ <: UniversalTrait]`.
    */
  private def isGenericArrayElement(tp: TypeOrWildcard)(using Context, SourceLanguage): Boolean =
    /** A symbol that represents the sort of JVM array that values of type `tp` can be stored in:
      * - If we can always store such values in a reference array, return `j.l.Object`.
      * - If we can always store them in a specific primitive array, return the corresponding primitive class.
      * - Otherwise, return `None`.
      */
    def arrayUpperBound(tp: Type): Option[ClassSymbol] = tp.dealias match
      case TypeRef.OfClass(cls) =>
        def isScala2SpecialCase: Boolean =
          summon[SourceLanguage] == SourceLanguage.Scala2
            && !cls.isNull
            && !cls.isSubClass(defn.ObjectClass)

        // Only a few classes have both primitives and references as subclasses.
        if cls.isAny || cls.isAnyVal || cls.isMatchable || cls.isSingleton || isScala2SpecialCase then None
        else if cls.isPrimitiveValueClass then Some(cls)
        else
          // Derived value classes in arrays are always boxed, so they end up here as well
          Some(defn.ObjectClass)

      case tp: TypeProxy =>
        arrayUpperBound(tp.translucentSuperType)
      case tp: AndType =>
        arrayUpperBound(tp.first).orElse(arrayUpperBound(tp.second))
      case tp: OrType =>
        val firstBound = arrayUpperBound(tp.first)
        val secondBound = arrayUpperBound(tp.first)
        if firstBound == secondBound then firstBound
        else None
      case _: NothingType | _: AnyKindType | _: TypeLambda =>
        None
      case tp: CustomTransientGroundType =>
        throw IllegalArgumentException(s"Unexpected transient type: $tp")
    end arrayUpperBound

    /** Can one of the JVM Array type store all possible values of type `tp`? */
    def fitsInJVMArray(tp: Type): Boolean = arrayUpperBound(tp).isDefined

    tp match
      case tp: WildcardTypeArg =>
        !fitsInJVMArray(tp.bounds.high)

      case tp: Type =>
        tp.dealias match
          case tp: TypeRef =>
            tp.optSymbol match
              case Some(cls: ClassSymbol) =>
                false
              case Some(sym: TypeMemberSymbol) if sym.isOpaqueTypeAlias =>
                isGenericArrayElement(tp.translucentSuperType)
              case _ =>
                tp.bounds match
                  case TypeAlias(alias)            => isGenericArrayElement(alias)
                  case AbstractTypeBounds(_, high) => !fitsInJVMArray(high)
          case tp: TypeParamRef =>
            !fitsInJVMArray(tp)
          case tp: MatchType =>
            val cases = tp.cases
            cases.nonEmpty && !fitsInJVMArray(cases.map(_.result).reduce(OrType(_, _)))
          case tp: TypeProxy =>
            isGenericArrayElement(tp.translucentSuperType)
          case tp: AndType =>
            isGenericArrayElement(tp.first) && isGenericArrayElement(tp.second)
          case tp: OrType =>
            isGenericArrayElement(tp.first) || isGenericArrayElement(tp.second)
          case _: NothingType | _: AnyKindType | _: TypeLambda =>
            false
          case tp: CustomTransientGroundType =>
            throw IllegalArgumentException(s"Unexpected transient type: $tp")
  end isGenericArrayElement

  /** The erased least upper bound of two erased types is computed as follows.
    *
    * - if both argument are arrays of objects, an array of the erased lub of the element types
    * - if both arguments are arrays of same primitives, an array of this primitive
    * - if one argument is array of primitives and the other is array of objects, Object
    * - if one argument is an array, Object
    * - otherwise a common superclass or trait S of the argument classes, with the
    *   following two properties:
    *     S is minimal: no other common superclass or trait derives from S
    *     S is last   : in the linearization of the first argument type `tp1`
    *                   there are no minimal common superclasses or traits that
    *                   come after S.
    * The reason to pick last is that we prefer classes over traits that way,
    * which leads to more predictable bytecode and (?) faster dynamic dispatch.
    */
  private def erasedLub(tp1: ErasedTypeRef, tp2: ErasedTypeRef)(using Context): ErasedTypeRef =
    def erasedObject: ClassRef = defn.ObjectClass.erasure

    (tp1, tp2) match
      case (ClassRef(cls1), ClassRef(cls2)) =>
        erasedClassRefLub(cls1, cls2).erasure
      case (ArrayTypeRef(ClassRef(base1), dims1), ArrayTypeRef(ClassRef(base2), dims2)) =>
        if dims1 != dims2 then erasedObject
        else if base1 == base2 then tp1
        else if base1.isPrimitiveValueClass || base2.isPrimitiveValueClass then erasedObject
        else ArrayTypeRef(erasedClassRefLub(base1, base2).erasure, dims1)
      case (ClassRef(cls1), tp2: ArrayTypeRef) =>
        if cls1 == defn.ErasedNothingClass || cls1.isNull then tp2
        else erasedObject
      case (tp1: ArrayTypeRef, ClassRef(cls2)) =>
        if cls2 == defn.ErasedNothingClass || cls2.isNull then tp1
        else erasedObject
  end erasedLub

  private def erasedClassRefLub(cls1: ClassSymbol, cls2: ClassSymbol)(using Context): ClassSymbol =
    if cls1 == cls2 then cls1
    else if cls1 == defn.ErasedNothingClass then cls2
    else if cls2 == defn.ErasedNothingClass then cls1
    else if cls1.isNull then
      if cls2.isSubClass(defn.ObjectClass) then cls2
      else defn.AnyClass
    else if cls2.isNull then
      if cls1.isSubClass(defn.ObjectClass) then cls1
      else defn.AnyClass
    else if cls1 == defn.ErasedBoxedUnitClass || cls2 == defn.ErasedBoxedUnitClass then defn.ObjectClass
    else
      /** takeWhile+1 */
      def takeUpTo[T](l: List[T])(f: T => Boolean): List[T] =
        @tailrec def loop(tail: List[T], acc: List[T]): List[T] =
          tail match
            case h :: t => loop(if f(h) then t else Nil, h :: acc)
            case Nil    => acc.reverse
        loop(l, Nil)
      end takeUpTo

      // We are not interested in anything that is not a supertype of cls2
      val cls2superclasses = cls1.linearization.filter(cls2.isSubClass(_))

      // From the spec, "Linearization also satisfies the property that a
      // linearization of a class always contains the linearization of its
      // direct superclass as a suffix"; it's enough to consider every
      // candidate up to the first class.
      val candidates = takeUpTo(cls2superclasses)(!_.isTrait)

      // Candidates such that "no other common superclass or trait derives from S"
      // TODO Also, drop `PairClass` since it is not valid after erasue
      val minimums = candidates.filter { candidate =>
        candidates.forall(x => !x.isSubClass(candidate) || (x eq candidate))
      }

      // Pick the last minimum to prioritize classes over traits
      minimums.lastOption.getOrElse(defn.ObjectClass)
  end erasedClassRefLub

  /** The erased greatest lower bound of two erased type picks one of the two argument types.
    *
    * This operation has the following the properties:
    * - Associativity and commutativity, because this method acts as the minimum
    *   of the total order induced by `compareErasedGlb`.
    */
  private def erasedGlb(tp1: PreErasedTypeRef, tp2: PreErasedTypeRef)(using Context): PreErasedTypeRef =
    if compareErasedGlb(tp1, tp2) <= 0 then tp1
    else tp2

  /** A comparison function that induces a total order on erased types,
    * where `A <= B` implies that the erasure of `A & B` should be A.
    *
    * This order respects the following properties:
    *
    * - ErasedValueTypes <= non-ErasedValueTypes
    * - arrays <= non-arrays
    * - primitives <= non-primitives
    * - real classes <= traits
    * - subtypes <= supertypes
    *
    * Since this isn't enough to order to unrelated classes, we use
    * lexicographic ordering of the class symbol's signature name as a
    * tie-breaker. This ensure that `A <= B && B <= A` iff `A =:= B`.
    *
    * Note that dotc uses the class symbol's `fullName`. Our `signatureName` is
    * precisely what corresponds to dotc's `fullName`, as a requirement.
    *
    * @see erasedGlb
    */
  private def compareErasedGlb(tp1: PreErasedTypeRef, tp2: PreErasedTypeRef)(using Context): Int =
    def compareClasses(cls1: ClassSymbol, cls2: ClassSymbol): Int =
      if cls1.isSubClass(cls2) then -1
      else if cls2.isSubClass(cls1) then 1
      else cls1.signatureName.toString.compareTo(cls2.signatureName.toString)
    end compareClasses

    (tp1, tp2) match
      case _ if tp1 == tp2 =>
        // fast path
        0

      case (ErasedValueClass(cls1, _), ErasedValueClass(cls2, _)) =>
        compareClasses(cls1, cls2)
      case (ErasedValueClass(cls1, _), _) =>
        -1
      case (_, ErasedValueClass(cls2, _)) =>
        1

      case (tp1: ArrayTypeRef, tp2: ArrayTypeRef) =>
        compareErasedGlb(tp1.elemType, tp2.elemType)
      case (_: ArrayTypeRef, _) =>
        -1
      case (_, _: ArrayTypeRef) =>
        1

      case (ClassRef(cls1), ClassRef(cls2)) =>
        val isPrimitive1 = cls1.isPrimitiveValueClass
        val isPrimitive2 = cls2.isPrimitiveValueClass
        if isPrimitive1 && isPrimitive2 then compareClasses(cls1, cls2)
        else if isPrimitive1 then -1
        else if isPrimitive2 then 1
        else
          val isRealClass1 = !cls1.isTrait
          val isRealClass2 = !cls2.isTrait
          if isRealClass1 && isRealClass2 then compareClasses(cls1, cls2)
          else if isRealClass1 then -1
          else if isRealClass2 then 1
          else compareClasses(cls1, cls2)
  end compareErasedGlb
end Erasure
