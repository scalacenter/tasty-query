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
  // TODO: improve this to match dotty:
  // - use correct type erasure algorithm from Scala 3, with specialisations
  //   for Java types and Scala 2 types (i.e. varargs, value-classes)

  @deprecated("use the overload that takes an explicit SourceLanguage", since = "0.7.1")
  def erase(tpe: Type)(using Context): ErasedTypeRef =
    erase(tpe, SourceLanguage.Scala3)

  def erase(tpe: Type, language: SourceLanguage)(using Context): ErasedTypeRef =
    erase(tpe, language, keepUnit = false)

  def erase(tpe: Type, language: SourceLanguage, keepUnit: Boolean)(using Context): ErasedTypeRef =
    given SourceLanguage = language
    finishErase(preErase(tpe, keepUnit))
  end erase

  /** First pass of erasure, where some special types are preserved as is.
    *
    * In particular, `Any` is preserved as `Any`, instead of becoming
    * `java.lang.Object`.
    */
  private def preErase(tpe: Type, keepUnit: Boolean)(using Context, SourceLanguage): ErasedTypeRef =
    def hasArrayErasure(cls: ClassSymbol): Boolean =
      cls.isArray || (cls.isRepeatedParamMagic && summon[SourceLanguage] == SourceLanguage.Java)

    def arrayOfBounds(bounds: TypeBounds): ErasedTypeRef =
      preErase(bounds.high, keepUnit = false) match
        case ClassRef(cls) if cls.isAny || cls.isAnyVal =>
          ClassRef(defn.ObjectClass)
        case typeRef =>
          typeRef.arrayOf()

    def arrayOf(tpe: TypeOrWildcard): ErasedTypeRef = tpe match
      case tpe: AppliedType =>
        tpe.tycon match
          case TypeRef.OfClass(cls) =>
            if hasArrayErasure(cls) then
              val List(targ) = tpe.args: @unchecked
              arrayOf(targ).arrayOf()
            else ClassRef(cls).arrayOf()
          case _ =>
            arrayOf(tpe.translucentSuperType)
      case TypeRef.OfClass(cls) =>
        if cls.isUnit then ClassRef(defn.ErasedBoxedUnitClass).arrayOf()
        else ClassRef(cls).arrayOf()
      case tpe: TypeRef =>
        tpe.optSymbol match
          case Some(sym: TypeMemberSymbol) =>
            sym.typeDef match
              case TypeMemberDefinition.TypeAlias(alias)          => arrayOf(alias)
              case TypeMemberDefinition.AbstractType(bounds)      => arrayOfBounds(bounds)
              case TypeMemberDefinition.OpaqueTypeAlias(_, alias) => arrayOf(alias)
          case _ =>
            arrayOfBounds(tpe.bounds)
      case tpe: TypeParamRef    => arrayOfBounds(tpe.bounds)
      case tpe: Type            => preErase(tpe, keepUnit = false).arrayOf()
      case tpe: WildcardTypeArg => arrayOfBounds(tpe.bounds)
    end arrayOf

    tpe match
      case tpe: AppliedType =>
        tpe.tycon match
          case TypeRef.OfClass(cls) =>
            if hasArrayErasure(cls) then
              val List(targ) = tpe.args: @unchecked
              arrayOf(targ)
            else ClassRef(cls)
          case _ =>
            preErase(tpe.translucentSuperType, keepUnit)
      case TypeRef.OfClass(cls) =>
        if !keepUnit && cls.isUnit then ClassRef(defn.ErasedBoxedUnitClass)
        else ClassRef(cls)
      case tpe: TypeRef =>
        tpe.optSymbol match
          case Some(sym: TypeMemberSymbol) =>
            sym.typeDef match
              case TypeMemberDefinition.OpaqueTypeAlias(_, alias) =>
                preErase(alias, keepUnit)
              case _ =>
                preErase(tpe.underlying, keepUnit)
          case _ =>
            preErase(tpe.underlying, keepUnit)
      case tpe: SingletonType =>
        preErase(tpe.underlying, keepUnit)
      case tpe: TypeParamRef =>
        preErase(tpe.bounds.high, keepUnit)
      case tpe: MatchType =>
        tpe.reduced match
          case Some(reduced) => preErase(reduced, keepUnit)
          case None          => preErase(tpe.bound, keepUnit)
      case tpe: OrType =>
        erasedLub(preErase(tpe.first, keepUnit = false), preErase(tpe.second, keepUnit = false))
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
        ClassRef(defn.PolyFunctionType.functionClassOf(mt))
      case tpe: RefinedType =>
        preErase(tpe.parent, keepUnit)
      case tpe: RecType =>
        preErase(tpe.parent, keepUnit)
      case _: ByNameType =>
        defn.Function0Class.erasure
      case _: NothingType =>
        defn.ErasedNothingClass.erasure
      case _: AnyKindType =>
        defn.ObjectClass.erasure
      case _: TypeLambda | _: CustomTransientGroundType =>
        throw IllegalArgumentException(s"Unexpected type in erasure: $tpe")
  end preErase

  private def finishErase(typeRef: ErasedTypeRef)(using Context): ErasedTypeRef =
    typeRef match
      case ClassRef(cls) =>
        if cls.isDerivedValueClass then finishEraseValueClass(cls)
        else cls.erasure
      case ArrayTypeRef(ClassRef(cls), dimensions) =>
        ArrayTypeRef(cls.erasure, dimensions)
  end finishErase

  private def finishEraseValueClass(cls: ClassSymbol)(using Context): ErasedTypeRef =
    val ctor = cls.findNonOverloadedDecl(nme.Constructor)

    def illegalConstructorType(): Nothing =
      throw InvalidProgramStructureException(s"Illegal value class constructor type ${ctor.declaredType.showBasic}")

    def ctorParamType(tpe: TypeOrMethodic): Type = tpe match
      case tpe: MethodType if tpe.paramTypes.sizeIs == 1 => tpe.paramTypes.head
      case tpe: MethodType                               => illegalConstructorType()
      case tpe: PolyType                                 => ctorParamType(tpe.resultType)
      case tpe: Type                                     => illegalConstructorType()

    erase(ctorParamType(ctor.declaredType), ctor.sourceLanguage)
  end finishEraseValueClass

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
    def erasedObject: ClassRef = ClassRef(defn.ObjectClass)

    (tp1, tp2) match
      case (ClassRef(cls1), ClassRef(cls2)) =>
        ClassRef(erasedClassRefLub(cls1, cls2))
      case (ArrayTypeRef(ClassRef(base1), dims1), ArrayTypeRef(ClassRef(base2), dims2)) =>
        if dims1 != dims2 then erasedObject
        else if base1 == base2 then tp1
        else if base1.isPrimitiveValueClass || base2.isPrimitiveValueClass then erasedObject
        else ArrayTypeRef(ClassRef(erasedClassRefLub(base1, base2)), dims1)
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
  private def erasedGlb(tp1: ErasedTypeRef, tp2: ErasedTypeRef)(using Context): ErasedTypeRef =
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
  private def compareErasedGlb(tp1: ErasedTypeRef, tp2: ErasedTypeRef)(using Context): Int =
    def compareClasses(cls1: ClassSymbol, cls2: ClassSymbol): Int =
      if cls1.isSubClass(cls2) then -1
      else if cls2.isSubClass(cls1) then 1
      else cls1.signatureName.toString.compareTo(cls2.signatureName.toString)
    end compareClasses

    (tp1, tp2) match
      case _ if tp1 == tp2 =>
        // fast path
        0

      case (ClassRef(cls1), _) if cls1.isDerivedValueClass =>
        tp2 match
          case ClassRef(cls2) if cls2.isDerivedValueClass =>
            compareClasses(cls1, cls2)
          case _ =>
            -1
      case (_, ClassRef(cls2)) if cls2.isDerivedValueClass =>
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
