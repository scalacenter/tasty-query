package tastyquery

import tastyquery.Contexts.*
import tastyquery.Symbols.*
import tastyquery.Types.*
import tastyquery.TypeMaps.*

private[tastyquery] object TypeOps:
  /** Is the given type dependent at all on the prefix it will be seen from?
    *
    * In other words, does it contain any `ThisType`?
    *
    * If not, there is no need to map it through `asSeenFrom`.
    */
  def isPrefixDependent(tp: TypeMappable): Boolean =
    existsPart(tp)(_.isInstanceOf[ThisType])

  def asSeenFrom(tp: TypeOrMethodic, pre: Prefix, cls: Symbol)(using Context): tp.ThisTypeMappableType =
    pre match
      case NoPrefix | _: PackageRef        => tp
      case pre: ThisType if pre.cls == cls => tp // This is necessary to cut down infinite recursions
      case pre: Type                       => new AsSeenFromMap(pre, cls).apply(tp)
  end asSeenFrom

  /** The TypeMap handling the asSeenFrom */
  private final class AsSeenFromMap(pre: Type, cls: Symbol)(using Context) extends ApproximatingTypeMap {

    /** Set to true when the result of `apply` was approximated to avoid an unstable prefix. */
    var approximated: Boolean = false

    def transform(tp: TypeMappable): TypeMappable = {

      /** Map a `C.this` type to the right prefix. If the prefix is unstable, and
        *  the current variance is <= 0, return a range.
        *  @param  pre     The prefix
        *  @param  cls     The class in which the `C.this` type occurs
        *  @param  thiscls The prefix `C` of the `C.this` type.
        */
      def toPrefix(origTp: ThisType, pre: Prefix, cls: Symbol, thiscls: ClassSymbol): Type =
        pre match
          case NoPrefix | _: PackageRef =>
            origTp
          case pre: SuperType =>
            toPrefix(origTp, pre.thistpe, cls, thiscls)
          case pre: Type =>
            cls match
              case cls: PackageSymbol =>
                origTp
              case cls: ClassSymbol =>
                if (thiscls.isSubClass(cls) && pre.baseType(thiscls).isDefined)
                  /*if (variance <= 0 && !isLegalPrefix(pre)) // isLegalPrefix always true?
                  if (variance < 0) {
                    approximated = true
                    NothingType
                  }
                  else
                    // Don't set the `approximated` flag yet: if this is a prefix
                    // of a path, we might be able to dealias the path instead
                    // (this is handled in `ApproximatingTypeMap`). If dealiasing
                    // is not possible, then `expandBounds` will end up being
                    // called which we override to set the `approximated` flag.
                    range(NothingType, pre)
                else*/ pre
                /*else if (pre.termSymbol.isPackage && !thiscls.isPackage)
                toPrefix(pre.select(nme.PACKAGE), cls, thiscls)*/
                else
                  pre.baseType(cls).flatMap(_.normalizedPrefix) match
                    case Some(normalizedPrefix) => toPrefix(origTp, normalizedPrefix, cls.owner.nn, thiscls)
                    case None                   => origTp
              case _ =>
                throw AssertionError(
                  s"While computing asSeenFrom for $origTp;\n"
                    + s"found unexpected cls = $cls in toPrefix($pre, $cls, $thiscls)"
                )
      end toPrefix

      tp match {
        case tp: ThisType =>
          toPrefix(tp, pre, cls, tp.cls)
        case _ =>
          mapOver(tp)
      }
    }

    override def reapply(tp: Type): Type =
      // derived infos have already been subjected to asSeenFrom, hence no need to apply the map again.
      tp

    override protected def expandBounds(tp: TypeBounds): Type = {
      approximated = true
      super.expandBounds(tp)
    }
  }

  // Folds over types

  def existsPart(tp: TypeMappable)(p: TypeMappable => Boolean): Boolean =
    new TypeFold[Boolean] {
      override def apply(z: Boolean, tp: TypeMappable): Boolean =
        z || p(tp) || super.apply(z, tp)
    }.apply(false, tp)
  end existsPart

  private class TypeFold[A] extends ((A, TypeMappable) => A):
    def apply(z: A, tp: TypeMappable): A = tp match
      case NoPrefix | _: PackageRef =>
        z

      case _: NothingType | _: AnyKindType | _: ThisType | _: ConstantType | _: ParamRef | _: RecThis =>
        z
      case tp: NamedType =>
        apply(z, tp.prefix)
      case tp: SuperType =>
        apply(z, tp.thistpe)
      case tp: AppliedType =>
        tp.args.foldLeft(apply(z, tp.tycon))(this)
      case tp: FlexibleType =>
        apply(z, tp.nonNullableType)
      case tp: ByNameType =>
        apply(z, tp.resultType)
      case tp: RepeatedType =>
        apply(z, tp.elemType)
      case tp: LambdaType =>
        apply(tp.paramInfos.foldLeft(z)(this), tp.resultType)
      case tp: AnnotatedType =>
        apply(z, tp.typ)
      case tp: TypeRefinement =>
        apply(apply(z, tp.parent), tp.refinedBounds)
      case tp: TermRefinement =>
        apply(apply(z, tp.parent), tp.refinedType)
      case tp: RecType =>
        apply(z, tp.parent)
      case tp: MatchType =>
        val z1 = apply(apply(z, tp.bound), tp.scrutinee)
        tp.cases.foldLeft(z1)(apply(_, _))
      case tp: SkolemType =>
        apply(z, tp.tpe)
      case tp: OrType =>
        apply(apply(z, tp.first), tp.second)
      case tp: AndType =>
        apply(apply(z, tp.first), tp.second)

      case tp: WildcardTypeArg =>
        apply(z, tp.bounds)

      case AbstractTypeBounds(low, high) =>
        apply(apply(z, low), high)
      case TypeAlias(alias) =>
        apply(z, alias)

      case tp: CustomTransientGroundType =>
        throw IllegalArgumentException(s"Unexpected custom transient type: $tp")
    end apply

    def apply(z: A, caze: MatchTypeCase): A =
      val z1 = caze.paramTypeBounds.foldLeft(z)(this)
      apply(apply(z1, caze.pattern), caze.result)
  end TypeFold

  // Tests around `matches`

  /** The implementation for `tp1.matches(tp2)`. */
  final def matchesType(tp1: TypeOrMethodic, tp2: TypeOrMethodic)(using Context): Boolean = tp1 match
    case tp1: MethodType =>
      tp2 match
        case tp2: MethodType =>
          // implicitness is ignored when matching
          matchingMethodParams(tp1, tp2)
            && matchesType(tp1.resultType, Substituters.substBinders(tp2.resultType, tp2, tp1))
        case _ =>
          tp1.paramNames.isEmpty
            && matchesType(tp1.resultType, tp2)

    case tp1: PolyType =>
      tp2 match
        case tp2: PolyType =>
          matchingPolyParams(tp1, tp2)
            && matchesType(tp1.resultType, Substituters.substBinders(tp2.resultType, tp2, tp1))
        case _ =>
          false

    case tp1: Type =>
      tp2 match
        case _: PolyType =>
          false
        case tp2: MethodType =>
          tp2.paramNames.isEmpty
            && matchesType(tp1, tp2.resultType)
        case _ =>
          true
  end matchesType

  /** Do the parameter types of `tp1` and `tp2` match in a way that allows `tp1` to override `tp2`?
    *
    * This is the case if they're pairwise `>:>`.
    */
  def matchingPolyParams(tp1: PolyType, tp2: PolyType)(using Context): Boolean =
    // TODO Actually test `>:>`.
    tp1.paramNames.lengthCompare(tp2.paramNames) == 0
  end matchingPolyParams

  /** Do the parameter types of `tp1` and `tp2` match in a way that allows `tp1` to override `tp2`?
    *
    * This is the case if they're pairwise `=:=`.
    */
  def matchingMethodParams(tp1: MethodType, tp2: MethodType)(using Context): Boolean =
    def loop(formals1: List[Type], formals2: List[Type]): Boolean = formals1 match
      case formal1 :: rest1 =>
        formals2 match
          case formal2 :: rest2 =>
            val formal2a = Substituters.substBinders(formal2, tp2, tp1)
            val paramsMatch = Subtyping.isSameType(formal2a, formal1)
            paramsMatch && loop(rest1, rest2)
          case Nil =>
            false

      case Nil =>
        formals2.isEmpty
    end loop

    loop(tp1.paramTypes, tp2.paramTypes)
  end matchingMethodParams

  // baseClasses

  /** The set of classes inherited by this type, in linearization order. */
  def baseClasses(tp: Type)(using Context): List[ClassSymbol] =
    tp match
      case TypeRef.OfClass(cls) =>
        cls.linearization

      case tp: TypeProxy =>
        baseClasses(tp.superType)

      case tp: AndType =>
        // Base classes are the merge of the operand base classes.
        val baseClasses1 = baseClasses(tp.first)
        val baseClasses1Set = baseClasses1.toSet

        def recur(baseClasses2: List[ClassSymbol]): List[ClassSymbol] = baseClasses2 match
          case baseClass2 :: baseClasses2Rest =>
            if baseClasses1Set.contains(baseClass2) then
              // Don't add baseClass2 since it's already there; shortcut altogether if it is not a trait
              if baseClass2.isTrait then recur(baseClasses2Rest)
              else baseClasses1 // common class, therefore the rest is the same in both sequences
            else
              // Include baseClass2 and continue
              baseClass2 :: recur(baseClasses2Rest)
          case Nil =>
            baseClasses1
        end recur

        recur(baseClasses(tp.second))

      case tp: OrType =>
        // Base classes are the intersection of the operand base classes.
        // scala.Null is ignored on both sides
        val baseClasses1 = baseClasses(tp.first).filter(!_.isNull)
        val baseClasses1Set = baseClasses1.toSet

        def recur(baseClasses2: List[ClassSymbol]): List[ClassSymbol] = baseClasses2 match
          case baseClass2 :: baseClasses2Rest =>
            if baseClasses1Set.contains(baseClass2) then
              // Include baseClass2 which is common; shortcut altogether if it is not a trait
              if baseClass2.isTrait then baseClass2 :: recur(baseClasses2Rest)
              else baseClasses2 // common class, therefore the rest is the same in both sequences
            else
              // Exclude baseClass2 and continue
              recur(baseClasses2Rest)
          case Nil =>
            Nil
        end recur

        recur(baseClasses(tp.second).filter(!_.isNull))

      case _: AnyKindType | _: NothingType | _: TypeLambda | _: CustomTransientGroundType =>
        Nil
  end baseClasses
end TypeOps
