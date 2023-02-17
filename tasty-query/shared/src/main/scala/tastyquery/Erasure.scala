package tastyquery

import scala.annotation.tailrec

import tastyquery.Contexts.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Types.*
import tastyquery.Types.ErasedTypeRef.*

private[tastyquery] object Erasure:
  // TODO: improve this to match dotty:
  // - use correct type erasure algorithm from Scala 3, with specialisations
  //   for Java types and Scala 2 types (i.e. varargs, value-classes)

  def erase(tpe: Type)(using Context): ErasedTypeRef =
    tpe match
      case _: ByNameType => ClassRef(defn.Function0Class)
      case _             => finishErase(preErase(tpe))
  end erase

  /** First pass of erasure, where some special types are preserved as is.
    *
    * In particular, `Any` is preserved as `Any`, instead of becoming
    * `java.lang.Object`.
    */
  private def preErase(tpe: Type)(using Context): ErasedTypeRef =
    def arrayOfBounds(bounds: TypeBounds): ErasedTypeRef =
      preErase(bounds.high) match
        case ClassRef(cls) if cls == defn.AnyClass || cls == defn.AnyValClass =>
          ClassRef(defn.ObjectClass)
        case typeRef =>
          typeRef.arrayOf()

    def arrayOf(tpe: Type): ErasedTypeRef = tpe match
      case tpe: AppliedType =>
        tpe.tycon match
          case TypeRef.OfClass(cls) =>
            if cls == defn.ArrayClass then
              val List(targ) = tpe.args: @unchecked
              arrayOf(targ).arrayOf()
            else ClassRef(cls).arrayOf()
          case _ =>
            arrayOf(tpe.translucentSuperType)
      case TypeRef.OfClass(cls) =>
        ClassRef(cls).arrayOf()
      case tpe: TypeRef =>
        tpe.optSymbol match
          case Some(sym: TypeMemberSymbol) =>
            sym.typeDef match
              case TypeMemberDefinition.TypeAlias(alias)          => arrayOf(alias)
              case TypeMemberDefinition.AbstractType(bounds)      => arrayOfBounds(bounds)
              case TypeMemberDefinition.OpaqueTypeAlias(_, alias) => arrayOf(alias)
          case _ =>
            arrayOfBounds(tpe.bounds)
      case tpe: TypeParamRef       => arrayOfBounds(tpe.bounds)
      case tpe: WildcardTypeBounds => arrayOfBounds(tpe.bounds)
      case _ =>
        preErase(tpe).arrayOf()
    end arrayOf

    tpe.widen match
      case tpe: AppliedType =>
        tpe.tycon match
          case TypeRef.OfClass(cls) =>
            if cls == defn.ArrayClass then
              val List(targ) = tpe.args: @unchecked
              arrayOf(targ)
            else ClassRef(cls)
          case _ =>
            preErase(tpe.translucentSuperType)
      case TypeRef.OfClass(cls) =>
        ClassRef(cls)
      case tpe: TypeRef =>
        tpe.optSymbol match
          case Some(sym: TypeMemberSymbol) =>
            sym.typeDef match
              case TypeMemberDefinition.OpaqueTypeAlias(_, alias) =>
                preErase(alias)
              case _ =>
                preErase(tpe.underlying)
          case _ =>
            preErase(tpe.underlying)
      case tpe: TypeParamRef =>
        preErase(tpe.bounds.high)
      case tpe: WildcardTypeBounds =>
        preErase(tpe.bounds.high)
      case tpe: OrType =>
        erasedLub(preErase(tpe.first), preErase(tpe.second))
      case tpe =>
        throw UnsupportedOperationException(s"Cannot erase $tpe")
  end preErase

  private def finishErase(typeRef: ErasedTypeRef)(using Context): ErasedTypeRef =
    def valueClass(cls: ClassSymbol): ErasedTypeRef =
      val ctor = cls.findNonOverloadedDecl(nme.Constructor)
      val List(Left(List(paramRef))) = ctor.paramRefss.dropWhile(_.isRight): @unchecked
      val paramType = paramRef.underlying
      erase(paramType)

    typeRef match
      case ClassRef(cls) =>
        if cls == defn.AnyValClass then ClassRef(defn.ObjectClass)
        else if cls.isDerivedValueClass then valueClass(cls)
        else cls.specialErasure.fold(typeRef)(f => f())
      case ArrayTypeRef(_, _) =>
        typeRef
  end finishErase

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
        else if defn.isPrimitiveValueClass(base1) || defn.isPrimitiveValueClass(base2) then erasedObject
        else ArrayTypeRef(ClassRef(erasedClassRefLub(base1, base2)), dims1)
      case (ClassRef(cls1), tp2: ArrayTypeRef) =>
        if cls1 == defn.NothingClass || cls1 == defn.NullClass then tp2
        else erasedObject
      case (tp1: ArrayTypeRef, ClassRef(cls2)) =>
        if cls2 == defn.NothingClass || cls2 == defn.NullClass then tp1
        else erasedObject
  end erasedLub

  private def erasedClassRefLub(cls1: ClassSymbol, cls2: ClassSymbol)(using Context): ClassSymbol =
    if cls1 == defn.NothingClass then cls2
    else if cls2 == defn.NothingClass then cls1
    else if cls1 == defn.NullClass then
      if cls2.isSubclass(defn.ObjectClass) then cls2
      else defn.AnyClass
    else if cls2 == defn.NullClass then
      if cls1.isSubclass(defn.ObjectClass) then cls1
      else defn.AnyClass
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
      val cls2superclasses = cls1.linearization.filter(cls2.isSubclass(_))

      // From the spec, "Linearization also satisfies the property that a
      // linearization of a class always contains the linearization of its
      // direct superclass as a suffix"; it's enough to consider every
      // candidate up to the first class.
      val candidates = takeUpTo(cls2superclasses)(!_.is(Trait))

      // Candidates such that "no other common superclass or trait derives from S"
      // TODO Also, drop `PairClass` since it is not valid after erasue
      val minimums = candidates.filter { candidate =>
        candidates.forall(x => !x.isSubclass(candidate) || (x eq candidate))
      }

      // Pick the last minimum to prioritize classes over traits
      minimums.lastOption.getOrElse(defn.ObjectClass)
  end erasedClassRefLub
end Erasure
