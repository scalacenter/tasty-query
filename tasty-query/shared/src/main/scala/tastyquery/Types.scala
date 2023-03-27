package tastyquery

import scala.annotation.{constructorOnly, tailrec, targetName}

import scala.collection.mutable
import scala.compiletime.uninitialized

import dotty.tools.tasty.TastyFormat.NameTags

import tastyquery.Annotations.*
import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Signatures.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Variances.*

object Types {
  private[tastyquery] final case class LookupIn(ownerRef: TypeRef, name: TermName)
  private[tastyquery] final case class LookupTypeIn(ownerRef: TypeRef, name: TypeName)

  private[tastyquery] final case class Scala2ExternalSymRef(owner: Symbol, path: List[Name]) {
    val name = path.last
  }

  enum ErasedTypeRef:
    case ClassRef(cls: ClassSymbol)
    case ArrayTypeRef(base: ClassRef, dimensions: Int)

    def toDebugString: String = this match
      case ClassRef(cls)                  => s"ClassRef(${cls.signatureName.toDebugString})"
      case ArrayTypeRef(base, dimensions) => s"ArrayTypeRef(${base.toDebugString}, $dimensions)"

    override def toString(): String = this match
      case ClassRef(cls)                  => cls.signatureName.toString()
      case ArrayTypeRef(base, dimensions) => base.toString() + "[]" * dimensions

    def arrayOf(): ArrayTypeRef = this match
      case classRef: ClassRef             => ArrayTypeRef(classRef, 1)
      case ArrayTypeRef(base, dimensions) => ArrayTypeRef(base, dimensions + 1)

    /** The `FullyQualifiedName` for this `ErasedTypeRef` as found in the `TermSig`s of `Signature`s. */
    def toSigFullName: FullyQualifiedName = this match
      case ClassRef(cls) =>
        cls.signatureName

      case ArrayTypeRef(base, dimensions) =>
        val suffix = "[]" * dimensions
        val baseName = base.cls.signatureName
        val suffixedLast = baseName.path.last match
          case TypeName(SuffixedName(NameTags.OBJECTCLASS, baseModuleName)) =>
            baseModuleName.asSimpleName.append(suffix).withObjectSuffix.toTypeName
          case last: TypeName =>
            last.toTermName.asSimpleName.append(suffix).toTypeName
          case last: TermName =>
            last.asSimpleName.append(suffix)
        FullyQualifiedName(baseName.path.init :+ suffixedLast)
    end toSigFullName
  end ErasedTypeRef

  object ErasedTypeRef:
    @deprecated("use the overload that takes an explicit SourceLanguage", since = "0.7.1")
    def erase(tpe: Type)(using Context): ErasedTypeRef =
      erase(tpe, SourceLanguage.Scala3)

    def erase(tpe: Type, language: SourceLanguage)(using Context): ErasedTypeRef =
      Erasure.erase(tpe, language)
  end ErasedTypeRef

  private[tastyquery] enum ResolveMemberResult:
    case NotFound
    case TermMember(symbols: List[TermSymbol], tpe: Type)
    case ClassMember(cls: ClassSymbol)
    case TypeMember(symbols: List[TypeSymbolWithBounds], bounds: TypeBounds)
  end ResolveMemberResult

  private[tastyquery] object ResolveMemberResult:
    def merge(leftResult: ResolveMemberResult, rightResult: ResolveMemberResult)(using Context): ResolveMemberResult =
      def mergeSyms[T <: TermOrTypeSymbol](leftSyms: List[T], rightSyms: List[T]): List[T] =
        val rightSyms1 = rightSyms.filter(sym => !leftSyms.exists(_.overrides(sym)))
        val leftSyms1 = leftSyms.filter(sym => !rightSyms1.exists(_.overrides(sym)))
        leftSyms1 ::: rightSyms1

      (leftResult, rightResult) match
        // When either side is NotFound, take the other side
        case (ResolveMemberResult.NotFound, right) =>
          right
        case (left, ResolveMemberResult.NotFound) =>
          left

        // Both cases are term members
        case (ResolveMemberResult.TermMember(leftSyms, leftTpe), ResolveMemberResult.TermMember(rightSyms, rightTpe)) =>
          val syms = mergeSyms(leftSyms, rightSyms)
          val tpe = leftTpe & rightTpe
          ResolveMemberResult.TermMember(syms, tpe)

        // When either side is a Class, take it
        case (left: ResolveMemberResult.ClassMember, _) =>
          left
        case (_, right: ResolveMemberResult.ClassMember) =>
          right

        // Both sides are type members
        case (
              ResolveMemberResult.TypeMember(leftSyms, leftBounds),
              ResolveMemberResult.TypeMember(rightSyms, rightBounds)
            ) =>
          val syms = mergeSyms(leftSyms, rightSyms)
          val bounds = leftBounds.intersect(rightBounds)
          ResolveMemberResult.TypeMember(syms, bounds)

        // Cases that cannot happen -- list them to preserve exhaustivity checking of every other case
        case unexpected @ (_: ResolveMemberResult.TermMember, _: ResolveMemberResult.TypeMember) =>
          throw MatchError(unexpected)
        case unexpected @ (_: ResolveMemberResult.TypeMember, _: ResolveMemberResult.TermMember) =>
          throw MatchError(unexpected)
    end merge
  end ResolveMemberResult

  /** A type parameter of a type constructor.
    *
    * Type parameters of polymorphic class types are [[Symbols.ClassTypeParamSymbol]]s.
    * For other type constructors, they are instances of an unspecified subclass.
    *
    * See [[Type.typeParams]].
    */
  trait TypeConstructorParam private[tastyquery] ():
    /** The variance of the type parameter. */
    def variance(using Context): Variance

    /** The name of the type parameter. */
    def name: TypeName

    /** The bounds of the type parameter. */
    def bounds(using Context): TypeBounds
  end TypeConstructorParam

  sealed trait TypeMappable:
    type ThisTypeMappableType >: this.type <: TypeMappable
  end TypeMappable

  sealed abstract class Prefix extends TypeMappable:
    type ThisTypeMappableType >: this.type <: Prefix

    final def select(sym: TermOrTypeSymbol)(using Context): NamedType =
      NamedType(this, sym) // dotc also calls reduceProjection here, should we do it?

    /** True iff `sym` is a symbol of a class type parameter and the reference
      * `<pre> . <sym>` is an actual argument reference, i.e., `pre` is not the
      * ThisType of `sym`'s owner, or a reference to `sym`'s owner.'
      */
    private[tastyquery] final def isArgPrefixOf(sym: ClassTypeParamSymbol)(using Context): Boolean =
      this match
        case tp: ThisType => tp.cls != sym.owner
        case tp: TypeRef  => !tp.optSymbol.exists(_ == sym.owner)
        case _            => true
    end isArgPrefixOf
  end Prefix

  object NoPrefix extends Prefix:
    type ThisTypeMappableType = this.type

    override def toString(): String = "NoPrefix"
  end NoPrefix

  /** A type in the Scala type system.
    *
    * Partitioned into [[GroundType]] and [[TypeProxy]].
    *
    * Also partitioned into [[TermType]], [[WildcardTypeBounds]] and
    * [[CustomTransientGroundType]].
    */
  sealed abstract class Type extends Prefix {
    type ThisTypeMappableType = Type

    final def isSubtype(that: Type)(using Context): Boolean =
      Subtyping.isSubtype(this, that)

    final def isSameType(that: Type)(using Context): Boolean =
      Subtyping.isSameType(this, that)

    /** The class symbol of this type, None if reduction is not possible */
    @tailrec
    private[tastyquery] final def classSymbol(using Context): Option[ClassSymbol] = this.widen match
      case TypeRef.OfClass(cls) =>
        Some(cls)
      case tpe: TypeRef =>
        tpe.optAliasedType match
          case Some(alias) => alias.classSymbol
          case None        => None
      case tpe: TypeProxy =>
        tpe.superType.classSymbol
      case _ =>
        None

    final def select(name: Name)(using Context): NamedType =
      NamedType(this, name)

    final def select(name: TermName)(using Context): TermRef =
      TermRef(this, name)

    final def select(name: TypeName)(using Context): TypeRef =
      TypeRef(this, name)

    final def lookupMember(name: Name)(using Context): Option[NamedType] =
      resolveMember(name, this) match
        case ResolveMemberResult.NotFound =>
          None
        case resolved: ResolveMemberResult.TermMember =>
          if resolved.symbols.isEmpty then None
          else Some(TermRef.fromResolved(this, resolved))
        case resolved: ResolveMemberResult.ClassMember =>
          Some(TypeRef.fromResolved(this, resolved))
        case resolved: ResolveMemberResult.TypeMember =>
          Some(TypeRef.fromResolved(this, name.asInstanceOf[TypeName], resolved))
    end lookupMember

    final def lookupMember(name: TermName)(using Context): Option[TermRef] =
      lookupMember(name: Name).map(_.asTerm)

    final def lookupMember(name: TypeName)(using Context): Option[TypeRef] =
      lookupMember(name: Name).map(_.asType)

    /** The type parameters of this type, if it is a type constructor.
      *
      * If this type is a type constructor, returns a non-empty list of its
      * type parameters.
      *
      * For all other types (proper types, any-kinded types, methodic types
      * and package refs), returns `Nil`.
      *
      * Special case: for `Nothing`, returns `Nil` as well (although `Nothing`
      * is universally-kinded, so it is a type constructor for all possible
      * type constructor signatures).
      */
    @tailrec
    final def typeParams(using Context): List[TypeConstructorParam] =
      this match
        case TypeRef.OfClass(cls) =>
          cls.typeParams
        case self: TypeRef =>
          self.underlying.typeParams
        case self: TypeLambda =>
          self.typeLambdaParams
        case self: AppliedType =>
          self.tycon match
            case TypeRef.OfClass(_) => Nil
            case _                  => self.superType.typeParams
        case self: TypeParamRef =>
          self.superType.typeParams
        case self: AnnotatedType =>
          self.superType.typeParams
        case self: WildcardTypeBounds =>
          self.bounds.high.typeParams
        case _: SingletonType | _: RefinedType | _: ByNameType | _: MatchType | _: RecType =>
          // These types are always proper types
          Nil
        case _: OrType | _: AndType =>
          // Should these inherit their typeParams when they are mergeable? (dotc does not do it)
          Nil
        case _: MethodicType | _: PackageRef | _: CustomTransientGroundType =>
          // For these types it does not really make sense to ask the question, but we return Nil anyway
          Nil
    end typeParams

    /** The type representing
      *
      *    T[U1, ..., Un]
      *
      * where
      * @param  this   = `T`
      * @param  args   = `U1,...,Un`
      */
    final def appliedTo(args: List[Type])(using Context): Type = {
      val typParams = this.typeParams
      val dealiased = this.dealias
      if (args.isEmpty)
        this
      else
        dealiased match {
          case dealiased: TypeLambdaType =>
            dealiased.instantiate(args)
          case dealiased: AndType =>
            dealiased.derivedAndType(dealiased.first.appliedTo(args), dealiased.second.appliedTo(args))
          case dealiased: OrType =>
            dealiased.derivedOrType(dealiased.first.appliedTo(args), dealiased.second.appliedTo(args))
          case dealiased: WildcardTypeBounds =>
            val newBounds = dealiased.bounds match
              case bounds @ TypeAlias(alias) =>
                bounds.derivedTypeAlias(alias.appliedTo(args))
              case bounds @ RealTypeBounds(low, high) =>
                bounds.derivedTypeBounds(low.appliedTo(args), high.appliedTo(args))
            dealiased.derivedWildcardTypeBounds(newBounds)
          case dealiased =>
            AppliedType(this, args)
        }
    }

    private[tastyquery] final def applyIfParameterized(args: List[Type])(using Context): Type =
      if (args.nonEmpty /*typeParams.nonEmpty*/ ) appliedTo(args) else this

    /** Substitute bound types by some other types */
    private[tastyquery] final def substParams(from: Binders, to: List[Type])(using Context): Type =
      Substituters.substParams(this, from, to)

    /** Substitute class type params by some other types. */
    private[tastyquery] final def substClassTypeParams(from: List[ClassTypeParamSymbol], to: List[Type])(
      using Context
    ): Type =
      Substituters.substClassTypeParams(this, from, to)

    /** Widen singleton types, ByNameTypes, AnnotatedTypes and RefinedTypes. */
    final def widen(using Context): Type = this match
      case _: TypeRef | _: MethodicType => this // fast path for most frequent cases
      case tp: TermRef                  => tp.underlying.widen // fast path for next most frequent case
      case tp: SingletonType            => tp.underlying.widen
      case tp: ByNameType               => tp.resultType.widen
      case tp: AnnotatedType            => tp.typ.widen
      case tp: RefinedType              => tp.parent.widen
      case tp                           => tp

    private[tastyquery] final def widenIfUnstable(using Context): Type = this match
      case tp: ByNameType                           => tp.resultType.widenIfUnstable
      case tp: TermRef if !tp.symbol.isStableMember => tp.underlying.widenIfUnstable
      case _                                        => this

    final def dealias(using Context): Type = dealias1(keepOpaques = true)

    private def dealias1(keepOpaques: Boolean)(using Context): Type = this match {
      case tp: TypeRef =>
        tp.optSymbol match
          case Some(tpSym: TypeMemberSymbol) =>
            tpSym.typeDef match
              case TypeMemberDefinition.TypeAlias(alias)                          => alias.dealias1(keepOpaques)
              case TypeMemberDefinition.OpaqueTypeAlias(_, alias) if !keepOpaques => alias.dealias1(keepOpaques)
              case _                                                              => tp
          case _ =>
            tp.optAliasedType match
              case Some(alias) => alias.dealias1(keepOpaques)
              case None        => tp
      case tp: AppliedType =>
        val tycon1 = tp.tycon.dealias1(keepOpaques)
        if (tycon1 ne tp.tycon) tp.superType.dealias1(keepOpaques)
        else this
      case tp: AnnotatedType =>
        tp.typ.dealias1(keepOpaques)
      case _ =>
        this
    }

    /** The normalized prefix of this type is:
      *
      * - For a type alias, the normalized prefix of its alias.
      * - For all other named type and class infos: the prefix.
      * - Inherited by all other type proxies.
      * - `None` for all other types.
      */
    @tailrec final def normalizedPrefix(using Context): Option[Prefix] = this match {
      case tp: TypeRef =>
        tp.optAliasedType match
          case Some(alias) => alias.normalizedPrefix
          case None        => Some(tp.prefix)
      case tp: TermRef =>
        Some(tp.prefix)
      case tp: TypeProxy =>
        tp.superType.normalizedPrefix
      case _ =>
        None
    }

    /** The basetype of this type with given class symbol.
      *
      * Returns `NoType` if this type does not have `base` in any of its base
      * types.
      */
    final def baseType(base: ClassSymbol)(using Context): Option[Type] =
      base.baseTypeOf(this)

    /** Find the member of this type with the given `name` when prefix `pre`. */
    private[tastyquery] def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult

    /** Finds the term member with the given signed name, disregarding the result type,
      * and whose type satisfies the given predicate.
      *
      * This method must follow the "paths" followed by `resolveMember`.
      * It is used when dealing with methodic refinements in
      * `Subtyping.hasMatchingRefinedMember`and `TermRefinement.resolveMember`.
      */
    private[tastyquery] def resolveMatchingMember(name: SignedName, pre: Type, typePredicate: Type => Boolean)(
      using Context
    ): ResolveMemberResult

    private[Types] def lookupRefined(name: Name)(using Context): Option[Type] =
      None // TODO

    final def asSeenFrom(pre: Prefix, cls: Symbol)(using Context): Type =
      TypeOps.asSeenFrom(this, pre, cls)

    /** Is this type exactly Nothing (no vars, aliases, refinements etc allowed)? */
    private[tastyquery] final def isExactlyNothing(using Context): Boolean = this match
      case tp: TypeRef =>
        tp.name == tpnme.Nothing && tp.isSpecificClass(defn.NothingClass)
      case _ =>
        false

    /** Is this type considered as "FromJavaObject" for the purposes of subtyping?
      *
      * See [Definitions.FromJavaObjectAlias] for details.
      */
    final def isFromJavaObject(using Context): Boolean =
      this match
        case tp: TypeRef =>
          if tp.optSymbol.contains(defn.FromJavaObjectAlias) then true
          else
            tp.optAliasedType match
              case Some(alias) => alias.isFromJavaObject
              case None        => false
        case _ =>
          false
    end isFromJavaObject

    /** The lower bound of a TypeBounds type, the type itself otherwise */
    private[tastyquery] final def lowerBound: Type = this match {
      case self: WildcardTypeBounds => self.bounds.low
      case _                        => this
    }

    /** The upper bound of a TypeBounds type, the type itself otherwise */
    private[tastyquery] final def upperBound: Type = this match {
      case self: WildcardTypeBounds => self.bounds.high
      case _                        => this
    }

    /** Is self type bounded by a type lambda or AnyKind? */
    private[tastyquery] final def isLambdaSub(using Context): Boolean = this match
      case TypeRef.OfClass(cls) =>
        cls == defn.AnyKindClass || cls.typeParams.nonEmpty
      case self: TypeRef =>
        self.underlying.isLambdaSub
      case self: AppliedType =>
        self.tycon match
          case TypeRef.OfClass(_) => false
          case _                  => self.superType.isLambdaSub
      case self: TypeLambda =>
        true
      case _: SingletonType | _: RefinedType | _: RecType =>
        false
      case self: WildcardTypeBounds =>
        self.upperBound.isLambdaSub
      case self: TypeProxy =>
        self.superType.isLambdaSub
      case _ =>
        false
    end isLambdaSub

    /** Is this type close enough to that type so that members with the two types would override each other?
      *
      * This means:
      *
      * - Either both types are polytypes with the same number of
      *   type parameters and their result types match after renaming
      *   corresponding type parameters
      * - Or both types are method types with `=:=`-equivalent(*) parameter types
      *   and matching result types after renaming corresponding parameter types
      *   if the method types are dependent.
      * - Or both types are `=:=`-equivalent
      * - Or neither type takes term or type parameters.
      *
      * (*) when matching with a Java method, we also regard Any and Object as equivalent parameter types. (TODO)
      *
      * This function will always use unsafe-nulls semamtics to check the types.
      * This is because we are using a relaxed rule (ignoring `Null` types)
      * to check overriding Java methods.
      */
    final def matches(that: Type)(using Context): Boolean =
      TypeOps.matchesType(this, that)

    // Combinators

    final def &(that: Type)(using Context): Type =
      // TypeComparer.glb(this, that)
      AndType.make(this, that)

    final def |(that: Type)(using Context): Type =
      // TypeCompare.lub(this, that)
      OrType.make(this, that)

    final def appliedTo(tpe: Type)(using Context): Type =
      this.appliedTo(tpe :: Nil)
  }

  // ----- Type categories ----------------------------------------------

  // Every type is expected to inherit either TypeProxy or GroundType.

  /** Type proxies.
    * Each implementation is expected to redefine the `underlying` method.
    */
  sealed abstract class TypeProxy extends Type {

    /** The type to which this proxy forwards operations. */
    def underlying(using Context): Type

    /** The closest supertype of this type.
      *
      * This is the same as `underlying`, except that
      *   - instead of a TypeBounds type it returns its upper bound, and
      *   - for applied types it returns the upper bound of the constructor re-applied to the arguments.
      */
    def superType(using Context): Type = underlying match {
      case wildcard: WildcardTypeBounds => wildcard.bounds.high
      case st                           => st
    }

    private[tastyquery] final def superTypeNormalized(using Context): Type =
      superType // .normalized

    /** Same as superType, except for two differences:
      *
      *  - opaque types are treated as transparent aliases
      *  - applied type are matchtype-reduced if possible
      *
      * Note: the reason to reduce match type aliases here and not in `superType`
      * is that `superType` is context-independent and cached, whereas matchtype
      * reduction depends on context and should not be cached (at least not without
      * the very specific cache invalidation condition for matchtypes).
      */
    def translucentSuperType(using Context): Type = superType

    private[tastyquery] def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult =
      underlying.resolveMember(name, pre)

    private[tastyquery] def resolveMatchingMember(name: SignedName, pre: Type, typePredicate: Type => Boolean)(
      using Context
    ): ResolveMemberResult =
      underlying.resolveMatchingMember(name, pre, typePredicate)
  }

  /** Non-proxy types */
  sealed abstract class GroundType extends Type

  /** Superclass for custom transient ground types used by custom algorithms.
    *
    * When writing algorithms that manipulate `Type`s, it is sometimes useful
    * to temporarily store custom data in place of `Type`s. This can be done
    * by defining a subclass of `CustomTransientGroundType`. At the end of the
    * day, all `CustomTransientGroundType`s should have been replaced by proper
    * `Type`s.
    *
    * The methods of `tasty-query` never expose instances of
    * `CustomTransientGroundType`, but you may use it for your own purposes.
    *
    * When permorming an exhaustive `match` on all possible `Type`s, you should
    * cover `CustomTransientGroundType` in a `case` that always throws (unless
    * you are actually using it for some purposes):
    *
    * ```scala
    * val tpe: Type = ...
    * tpe match
    *   case tpe: TypeRef => ...
    *   ...
    *   case tpe: CustomTransientGroundType =>
    *     throw AssertionError(s"Unexpected custom transient ground type $tpe")
    * end match
    * ```
    */
  abstract class CustomTransientGroundType extends GroundType:
    private[tastyquery] final def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult =
      throw AssertionError(s"Trying to findMember($name, $pre) on $this")

    private[tastyquery] def resolveMatchingMember(name: SignedName, pre: Type, typePredicate: Type => Boolean)(
      using Context
    ): ResolveMemberResult =
      throw AssertionError(s"Trying to call resolveMatchingMember($name, $pre) on $this")
  end CustomTransientGroundType

  // ----- Marker traits ------------------------------------------------

  /** A marker trait for types that can be the type of a [[Trees.TermTree]].
    *
    * The only standard [[Type]] that is not a [[TermType]] is [[WildcardTypeBounds]].
    *
    * Partitioned into [[ValueType]], [[MethodicType]], [[ByNameType]] and
    * [[PackageRef]].
    */
  sealed trait TermType extends Type

  /** The type of a `def` that has at least one (term or type) parameter list.
    *
    * Partitioned into [[MethodType]] and [[PolyType]].
    */
  sealed trait MethodicType extends GroundType with TermType

  /** A marker trait for the type of values.
    *
    * Most [[TermType]]s are [[ValueType]]. The only exceptions are
    * [[MethodicType]], [[ByNameType]] and [[PackageRef]].
    */
  sealed trait ValueType extends TermType

  /** A marker trait for types that are guaranteed to contain only a
    * single non-null value (they might contain null in addition).
    */
  sealed trait SingletonType extends TypeProxy with ValueType:
    private[tastyquery] final def isStable(using Context): Boolean = this match
      case tp: TermRef => tp.symbol.isStableMember
      case _           => true
  end SingletonType

  // ----- Type Proxies -------------------------------------------------

  sealed abstract class NamedType extends TypeProxy with ValueType {
    protected type AnyDesignatorType = TermOrTypeSymbol | Name | LookupIn | LookupTypeIn | Scala2ExternalSymRef

    type ThisName <: Name
    type ThisSymbolType <: TermOrTypeSymbol { type ThisNameType = ThisName }
    type ThisNamedType >: this.type <: NamedType
    protected type ThisDesignatorType >: ThisSymbolType <: AnyDesignatorType

    val prefix: Prefix

    protected def designator: ThisDesignatorType

    // For tests
    private[tastyquery] final def designatorInternal: AnyDesignatorType =
      designator

    private var myName: ThisName | Null = null

    private[tastyquery] final def isLocalRef(sym: Symbol): Boolean =
      prefix == NoPrefix && (designator eq sym)

    private[tastyquery] final def isSomeClassTypeParamRef: Boolean =
      designator.isInstanceOf[ClassTypeParamSymbol]

    private[tastyquery] final def isClassTypeParamRef(sym: ClassTypeParamSymbol): Boolean =
      designator eq sym

    private[tastyquery] final def isTypeParamRef(tparam: TypeConstructorParam): Boolean =
      designator eq tparam

    final def isType: Boolean = isInstanceOf[TypeRef]

    final def isTerm: Boolean = isInstanceOf[TermRef]

    private[tastyquery] final def asTerm: TermRef = this.asInstanceOf[TermRef]
    private[tastyquery] final def asType: TypeRef = this.asInstanceOf[TypeRef]

    /** If designator is a name, this name. Otherwise, the original name
      * of the designator symbol.
      */
    final def name: ThisName = {
      val local = myName
      if local == null then
        val computed = computeName
        myName = computed
        computed
      else local.asInstanceOf[ThisName] // do not remove - it is needed to satisfy the debugger's expression evaluator
    }

    private def computeName: ThisName = (designator match {
      case name: Name                       => name
      case sym: TermOrTypeSymbol            => sym.name
      case LookupIn(_, name)                => name
      case LookupTypeIn(_, name)            => name
      case designator: Scala2ExternalSymRef => designator.name
    }).asInstanceOf[ThisName]

    def optSymbol(using Context): Option[ThisSymbolType]

    /** A selection of the same kind, but with potentially a different prefix.
      * The following normalization is performed for type selections T#A:
      *
      *    T#A --> B    if A is bound to an alias `= B` in T
      */
    private[tastyquery] final def normalizedDerivedSelect(prefix: Type)(using Context): Type =
      if (prefix eq this.prefix) this
      else if (prefix.isExactlyNothing) prefix
      else normalizedDerivedSelectImpl(prefix)

    protected def normalizedDerivedSelectImpl(prefix: Type)(using Context): Type

    private[tastyquery] final def derivedSelect(prefix: Prefix): ThisNamedType =
      if prefix eq this.prefix then this
      else withPrefix(prefix)

    protected def withPrefix(prefix: Prefix): ThisNamedType
  }

  object NamedType {

    private[tastyquery] def possibleSelFromPackage(prefix: Type, name: TermName)(
      using Context
    ): (TermRef | PackageRef) =
      prefix match
        case prefix: PackageRef if name.isInstanceOf[SimpleName] =>
          prefix.symbol.getPackageDecl(name.asSimpleName) match
            case Some(nested) => PackageRef(nested)
            case _            => TermRef(prefix, name)
        case prefix =>
          TermRef(prefix, name)
    end possibleSelFromPackage

    def apply(prefix: Prefix, sym: TermOrTypeSymbol)(using Context): NamedType =
      sym match
        case sym: TypeSymbol => TypeRef(prefix, sym)
        case sym: TermSymbol => TermRef(prefix, sym)

    def apply(prefix: Type, name: Name)(using Context): NamedType =
      name match
        case name: TypeName => TypeRef(prefix, name)
        case name: TermName => TermRef(prefix, name)

    private[tastyquery] def apply(prefix: Prefix, external: Scala2ExternalSymRef)(using Context): NamedType =
      external.name match
        case _: TypeName => TypeRef(prefix, external)
        case _: TermName => TermRef(prefix, external)

    private[tastyquery] def resolveScala2ExternalRef(externalRef: Scala2ExternalSymRef)(using Context): Symbol =
      externalRef.path.foldLeft(externalRef.owner) { (owner, name) =>
        /* In Scala 2 external references, (term) *modules* can appear in paths.
         * When we find one, in our system, we must follow through to their module class
         * instead. The `declaredType` will in that case always be a `TypeRef` to the
         * module class.
         * Terms cannot otherwise appear in paths.
         */
        val cls = if owner.isTerm then owner.asTerm.declaredType.asInstanceOf[TypeRef].asClass else owner
        cls.asDeclaringSymbol.getDecl(name).getOrElse {
          throw new MemberNotFoundException(owner, name)
        }
      }
    end resolveScala2ExternalRef
  }

  /** The singleton type for path prefix#myDesignator. */
  final class TermRef private (
    val prefix: Prefix,
    private var myDesignator: TermSymbol | TermName | LookupIn | Scala2ExternalSymRef
  ) extends NamedType
      with SingletonType {

    type ThisName = TermName
    type ThisSymbolType = TermSymbol
    type ThisNamedType = TermRef
    protected type ThisDesignatorType = TermSymbol | TermName | LookupIn | Scala2ExternalSymRef

    // Cache fields
    private var mySymbol: TermSymbol | Null = null
    private var myUnderlying: Type | Null = null
    private var mySignature: Signature | Null = null

    private def this(prefix: Type, resolved: ResolveMemberResult.TermMember) =
      this(prefix, resolved.symbols.head)
      mySymbol = resolved.symbols.head
      myUnderlying = resolved.tpe
    end this

    protected def designator: ThisDesignatorType = myDesignator

    override def toString(): String =
      s"TermRef($prefix, $myDesignator)"

    final def symbol(using Context): TermSymbol =
      if mySymbol == null then resolve()
      mySymbol.asInstanceOf[TermSymbol]

    private def resolve()(using Context): Unit =
      def storeResolved(sym: TermSymbol, tpe: Type): Unit =
        mySymbol = sym
        myDesignator = sym
        myUnderlying = tpe

      designator match
        case sym: TermSymbol =>
          storeResolved(sym, sym.declaredTypeAsSeenFrom(prefix))
        case lookupIn: LookupIn =>
          val sym = TermRef.resolveLookupIn(lookupIn)
          storeResolved(sym, sym.declaredTypeAsSeenFrom(prefix))
        case externalRef: Scala2ExternalSymRef =>
          val sym = NamedType.resolveScala2ExternalRef(externalRef).asTerm
          storeResolved(sym, sym.declaredTypeAsSeenFrom(prefix))
        case name: TermName =>
          prefix match
            case prefix: Type =>
              prefix.resolveMember(name, prefix) match
                case ResolveMemberResult.TermMember(symbols, tpe) if symbols.nonEmpty =>
                  storeResolved(symbols.head, tpe)
                case _ =>
                  throw MemberNotFoundException(prefix, name)
            case NoPrefix =>
              throw new AssertionError(s"found reference by name $name without a prefix")
    end resolve

    final def optSymbol(using Context): Option[TermSymbol] =
      Some(symbol)

    override def underlying(using ctx: Context): Type =
      if myUnderlying == null then resolve()
      myUnderlying.asInstanceOf[Type]

    private[tastyquery] final def signature(using Context): Signature =
      val local = mySignature
      if local != null then local
      else
        val computed = symbol.signature
        mySignature = computed
        computed
    end signature

    private[tastyquery] override def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult =
      underlying match
        case mt: MethodType if mt.paramInfos.isEmpty /*&& symbol.is(StableRealizable)*/ =>
          mt.resultType.resolveMember(name, pre)
        case tp =>
          tp.resolveMember(name, pre)
    end resolveMember

    private[tastyquery] override def resolveMatchingMember(name: SignedName, pre: Type, typePredicate: Type => Boolean)(
      using Context
    ): ResolveMemberResult =
      underlying match
        case mt: MethodType if mt.paramInfos.isEmpty /*&& symbol.is(StableRealizable)*/ =>
          mt.resultType.resolveMatchingMember(name, pre, typePredicate)
        case tp =>
          tp.resolveMatchingMember(name, pre, typePredicate)
    end resolveMatchingMember

    protected final def normalizedDerivedSelectImpl(prefix: Type)(using Context): TermRef =
      designator match
        case sym: TermSymbol if !sym.is(Private) =>
          TermRef(prefix, sym.signedName)
        case desig =>
          withPrefix(prefix)
    end normalizedDerivedSelectImpl

    protected final def withPrefix(prefix: Prefix): TermRef =
      new TermRef(prefix, designator)
  }

  object TermRef:
    def apply(prefix: Type, name: TermName): TermRef = new TermRef(prefix, name)
    def apply(prefix: Prefix, symbol: TermSymbol): TermRef = new TermRef(prefix, symbol)

    private[tastyquery] def apply(prefix: Type, designator: LookupIn): TermRef = new TermRef(prefix, designator)

    private[tastyquery] def apply(prefix: Prefix, external: Scala2ExternalSymRef): TermRef =
      new TermRef(prefix, external)

    private[Types] def fromResolved(prefix: Type, resolved: ResolveMemberResult.TermMember): TermRef =
      new TermRef(prefix, resolved)

    private[tastyquery] def resolveLookupIn(designator: LookupIn)(using Context): TermSymbol =
      val cls = designator.ownerRef.classSymbol.getOrElse {
        throw InvalidProgramStructureException(s"Owner of SelectIn($designator) does not refer a class")
      }
      cls
        .findMember(cls.thisType, designator.name)
        .getOrElse {
          throw MemberNotFoundException(cls, designator.name)
        }
        .asTerm
    end resolveLookupIn
  end TermRef

  final class PackageRef(val fullyQualifiedName: FullyQualifiedName) extends GroundType with TermType {
    private var packageSymbol: PackageSymbol | Null = null

    def this(packageSym: PackageSymbol) =
      this(packageSym.fullName)
      packageSymbol = packageSym

    def symbol(using Context): PackageSymbol = {
      val local = packageSymbol
      if (local == null) {
        val resolved = ctx.findPackageFromRoot(fullyQualifiedName)
        packageSymbol = resolved
        resolved
      } else local
    }

    private[tastyquery] def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult =
      val sym = symbol.getDecl(name).orElse {
        /* #179 For some very unfortunate reason, Scala 3 emits TypeRefs
         * whose prefix is a PackageRef but the name references something in a
         * *package object*. That goes contrary to TASTy's purpose of being a
         * fully-resolved thing. We have to work around it here.
         * This is very annoying because we have to load a bunch of things that
         * may not be necessary.
         */
        symbol.allPackageObjectDecls().iterator.flatMap(_.getDecl(name)).nextOption()
      }

      sym match
        case Some(sym: TermSymbol) =>
          ResolveMemberResult.TermMember(sym :: Nil, sym.declaredTypeAsSeenFrom(pre))
        case Some(sym: ClassSymbol) =>
          ResolveMemberResult.ClassMember(sym)
        case Some(sym: TypeSymbolWithBounds) =>
          ResolveMemberResult.TypeMember(sym :: Nil, sym.boundsAsSeenFrom(pre))
        case Some(sym: PackageSymbol) =>
          ResolveMemberResult.NotFound // maybe we should eagerly throw here?
        case None =>
          ResolveMemberResult.NotFound
    end resolveMember

    private[tastyquery] def resolveMatchingMember(name: SignedName, pre: Type, typePredicate: Type => Boolean)(
      using Context
    ): ResolveMemberResult =
      /* Until proven otherwise, we assume that PackageRef's cannot participate
       * as valid subtypes of `TermRefinement`s, and that therefore we can
       * always return `NotFound` here.
       */
      ResolveMemberResult.NotFound
    end resolveMatchingMember

    override def toString(): String = s"PackageRef($fullyQualifiedName)"
  }

  final class TypeRef private (
    val prefix: Prefix,
    private var myDesignator: TypeName | TypeSymbol | LookupTypeIn | Scala2ExternalSymRef
  ) extends NamedType {

    type ThisName = TypeName
    type ThisSymbolType = TypeSymbol
    type ThisNamedType = TypeRef
    type ThisDesignatorType = TypeName | TypeSymbol | LookupTypeIn | Scala2ExternalSymRef

    // Cache fields
    private var myOptSymbol: Option[TypeSymbol] | Null = null
    private var myBounds: TypeBounds | Null = null

    private def this(prefix: Type, resolved: ResolveMemberResult.ClassMember) =
      this(prefix, resolved.cls)
      myOptSymbol = Some(resolved.cls)
    end this

    private def this(prefix: Type, name: TypeName, resolved: ResolveMemberResult.TypeMember) =
      this(prefix, name)
      val optSymbol = resolved.symbols.headOption
      myOptSymbol = optSymbol
      if optSymbol.isDefined then myDesignator = optSymbol.get
      myBounds = resolved.bounds
    end this

    protected def designator: ThisDesignatorType = myDesignator

    override def toString(): String =
      s"TypeRef($prefix, $myDesignator)"

    private def ensureResolved()(using Context): Unit =
      if myOptSymbol == null then resolve()

    private def resolve()(using Context): Unit =
      def storeClass(cls: ClassSymbol): Unit =
        myOptSymbol = Some(cls)
        myDesignator = cls

      def storeTypeMember(sym: Option[TypeSymbolWithBounds], bounds: TypeBounds): Unit =
        myOptSymbol = sym
        if sym.isDefined then myDesignator = sym.get
        myBounds = bounds

      def storeSymbol(sym: TypeSymbol): Unit = sym match
        case cls: ClassSymbol          => storeClass(cls)
        case sym: TypeSymbolWithBounds => storeTypeMember(Some(sym), sym.boundsAsSeenFrom(prefix))

      designator match
        case sym: TypeSymbol =>
          storeSymbol(sym)
        case lookupTypeIn: LookupTypeIn =>
          val sym = TypeRef.resolveLookupTypeIn(lookupTypeIn)
          storeSymbol(sym)
        case externalRef: Scala2ExternalSymRef =>
          val sym = NamedType.resolveScala2ExternalRef(externalRef).asType
          storeSymbol(sym)
        case name: TypeName =>
          prefix match
            case prefix: Type =>
              prefix.resolveMember(name, prefix) match
                case ResolveMemberResult.ClassMember(cls) =>
                  storeClass(cls)
                case ResolveMemberResult.TypeMember(symbols, bounds) =>
                  storeTypeMember(symbols.headOption, bounds)
                case _ =>
                  throw MemberNotFoundException(prefix, name)
            case NoPrefix =>
              throw new AssertionError(s"found reference by name $name without a prefix")
    end resolve

    final def optSymbol(using Context): Option[TypeSymbol] =
      ensureResolved()
      myOptSymbol.nn

    final def isClass(using Context): Boolean =
      optSymbol.exists(_.isClass)

    private[tastyquery] final def asClass(using Context): ClassSymbol =
      optSymbol.get.asClass

    private[tastyquery] final def isSpecificClass(cls: ClassSymbol)(using Context): Boolean =
      optSymbol.contains(cls)

    override def underlying(using Context): Type =
      bounds.high

    final def bounds(using Context): TypeBounds =
      ensureResolved()
      val local = myBounds
      if local == null then
        throw AssertionError(s"TypeRef $this has no `underlying` because it refers to a `ClassSymbol`")
      else local

    def typeDef(using Context): TypeMemberDefinition = optSymbol match
      case Some(sym: TypeMemberSymbol) => sym.typeDef
      case _ =>
        throw AssertionError(s"No typeDef for $this")

    def optAliasedType(using Context): Option[Type] =
      ensureResolved()
      myBounds match
        case TypeAlias(alias) => Some(alias)
        case _                => None

    override def translucentSuperType(using Context): Type = optSymbol match
      case Some(sym: TypeMemberSymbol) =>
        sym.typeDef match
          case TypeMemberDefinition.OpaqueTypeAlias(_, alias) => alias
          case _                                              => underlying
      case _ =>
        underlying
    end translucentSuperType

    private[tastyquery] override def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult =
      optSymbol match
        case Some(sym: ClassSymbol) =>
          sym.resolveMember(name, pre)
        case _ =>
          underlying.resolveMember(name, pre)

    private[tastyquery] override def resolveMatchingMember(name: SignedName, pre: Type, typePredicate: Type => Boolean)(
      using Context
    ): ResolveMemberResult =
      optSymbol match
        case Some(sym: ClassSymbol) =>
          sym.resolveMatchingMember(name, pre, typePredicate)
        case _ =>
          underlying.resolveMatchingMember(name, pre, typePredicate)
    end resolveMatchingMember

    protected final def normalizedDerivedSelectImpl(prefix: Type)(using Context): Type =
      val result1 = optSymbol match
        case Some(sym: ClassTypeParamSymbol) => sym.argForParam(prefix)
        case _                               => prefix.lookupRefined(name)

      result1 match
        case Some(res) =>
          res
        case None =>
          designator match
            case sym: TypeMemberSymbol if !sym.is(Private) =>
              TypeRef(prefix, sym.name)
            case desig =>
              withPrefix(prefix)
    end normalizedDerivedSelectImpl

    protected final def withPrefix(prefix: Prefix): TypeRef =
      new TypeRef(prefix, designator)
  }

  object TypeRef:
    def apply(prefix: Type, name: TypeName): TypeRef = new TypeRef(prefix, name)
    def apply(prefix: Prefix, symbol: TypeSymbol): TypeRef = new TypeRef(prefix, symbol)

    private[tastyquery] def apply(prefix: Type, lookupTypeIn: LookupTypeIn): TypeRef =
      new TypeRef(prefix, lookupTypeIn)

    private[tastyquery] def apply(prefix: Prefix, external: Scala2ExternalSymRef): TypeRef =
      new TypeRef(prefix, external)

    private[Types] def fromResolved(prefix: Type, resolved: ResolveMemberResult.ClassMember): TypeRef =
      new TypeRef(prefix, resolved)

    private[Types] def fromResolved(prefix: Type, name: TypeName, resolved: ResolveMemberResult.TypeMember): TypeRef =
      new TypeRef(prefix, name, resolved)

    private[tastyquery] object OfClass:
      def unapply(typeRef: TypeRef)(using Context): Option[ClassSymbol] =
        typeRef.optSymbol match
          case Some(cls: ClassSymbol) => Some(cls)
          case _                      => None
    end OfClass

    private[tastyquery] def resolveLookupTypeIn(designator: LookupTypeIn)(using Context): TypeSymbol =
      val cls = designator.ownerRef.classSymbol.getOrElse {
        throw InvalidProgramStructureException(s"Owner of LookupTypeIn($designator) does not refer a class")
      }
      cls.typeParams
        .find(_.name == designator.name) // typical case, resulting from persisted capture conversion
        .orElse(cls.getDecl(designator.name)) // reference to private class member, or shadowed class member
        .getOrElse {
          throw MemberNotFoundException(cls, designator.name)
        }
    end resolveLookupTypeIn
  end TypeRef

  final class ThisType(val tref: TypeRef) extends SingletonType {
    private var myUnderlying: Type | Null = null

    override def underlying(using Context): Type =
      val local = myUnderlying
      if local != null then local
      else
        val cls = this.cls
        val computed =
          if cls.isStatic then cls.selfType
          else cls.selfType.asSeenFrom(tref.prefix, cls)
        myUnderlying = computed
        computed
    end underlying

    final def cls(using Context): ClassSymbol = tref.asClass

    override def toString(): String = s"ThisType($tref)"
  }

  /** The type of a super reference cls.super where
    * `thistpe` is cls.this and `supertpe` is the type of the value referenced
    * by `super`.
    */
  final class SuperType(val thistpe: ThisType, val explicitSupertpe: Option[Type]) extends TypeProxy with SingletonType:
    private var mySupertpe: Type | Null = explicitSupertpe.orNull

    final def supertpe(using Context): Type =
      val local = mySupertpe
      if local != null then local
      else
        val computed = thistpe.cls.parents.reduceLeft(_ & _)
        mySupertpe = computed
        computed
    end supertpe

    override def underlying(using Context): Type = supertpe

    override def superType(using Context): Type =
      val superCls = supertpe match
        case supertpe: TypeRef => supertpe.asClass
        case _                 => throw AssertionError(s"Cannot compute super class for $this")
      thistpe.baseType(superCls).getOrElse {
        throw AssertionError(s"Cannot find baseType for $this")
      }
    end superType

    override def toString(): String = s"SuperType($thistpe, $explicitSupertpe)"
  end SuperType

  /** A constant type with single `value`. */
  final class ConstantType(val value: Constant) extends TypeProxy with SingletonType {
    override def underlying(using Context): Type =
      value.wideType

    override def toString(): String = s"ConstantType($value)"
  }

  /** A type application `C[T_1, ..., T_n]`
    * Typebounds for wildcard application: C[_], C[?]
    */
  final class AppliedType(val tycon: Type, val args: List[Type]) extends TypeProxy with ValueType {
    override def underlying(using Context): Type = tycon

    override def superType(using Context): Type =
      tycon match
        //case tycon: HKTypeLambda => defn.AnyType
        case TypeRef.OfClass(_) => tycon
        case tycon: TypeProxy   => tycon.superType.applyIfParameterized(args)
        case _                  => defn.AnyType

    override def translucentSuperType(using Context): Type = tycon match
      case tycon: TypeRef if tycon.optSymbol.exists(_.isOpaqueTypeAlias) =>
        tycon.translucentSuperType.applyIfParameterized(args)
      case _ =>
        // tryNormalize.orElse(superType) // TODO for match types
        superType

    private[tastyquery] def tyconTypeParams(using Context): List[TypeConstructorParam] =
      val tparams = tycon.typeParams
      /*if (tparams.isEmpty) HKTypeLambda.any(args.length).typeParams else*/
      tparams

    /** Is this an unreducible application to wildcard arguments?
      * This is the case if tycon is higher-kinded. This means
      * it is a subtype of a hk-lambda, but not a match alias.
      * (normal parameterized aliases are removed in `appliedTo`).
      * Applications of higher-kinded type constructors to wildcard arguments
      * are equivalent to existential types, which are not supported.
      */
    private[tastyquery] final def isUnreducibleWild(using Context): Boolean =
      // TODO tycon.isLambdaSub && hasWildcardArg && !isMatchAlias
      false

    private[tastyquery] override def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult =
      tycon match
        case tycon @ TypeRef.OfClass(_) =>
          tycon.resolveMember(name, pre)
        case _ =>
          superType.resolveMember(name, pre)
    end resolveMember

    private[tastyquery] override def resolveMatchingMember(name: SignedName, pre: Type, typePredicate: Type => Boolean)(
      using Context
    ): ResolveMemberResult =
      tycon match
        case tycon @ TypeRef.OfClass(_) =>
          tycon.resolveMatchingMember(name, pre, typePredicate)
        case _ =>
          superType.resolveMatchingMember(name, pre, typePredicate)
    end resolveMatchingMember

    private[tastyquery] final def derivedAppliedType(tycon: Type, args: List[Type]): AppliedType =
      if ((tycon eq this.tycon) && (args eq this.args)) this
      else AppliedType(tycon, args)

    private[tastyquery] final def map(op: Type => Type): AppliedType =
      derivedAppliedType(op(tycon), args.mapConserve(op))

    override def toString(): String = s"AppliedType($tycon, $args)"
  }

  /** A by-name parameter type of the form `=> T`. */
  final class ByNameType(val resultType: Type) extends TypeProxy with TermType {
    override def underlying(using Context): Type = resultType

    private[tastyquery] final def derivedByNameType(resultType: Type): ByNameType =
      if (resultType eq this.resultType) this else ByNameType(resultType)

    override def toString(): String = s"ByNameType($resultType)"
  }

  sealed trait LambdaType extends ParamRefBinders with TermType {
    type ThisName <: Name
    type PInfo <: Type | TypeBounds
    type This <: LambdaType { type PInfo = LambdaType.this.PInfo }
    type ParamRefType <: ParamRef

    def paramNames: List[ThisName]
    def paramInfos: List[PInfo]
    def resultType: Type

    protected def newParamRef(n: Int): ParamRefType

    val paramRefs: List[ParamRefType] =
      List.tabulate(paramNames.size)(newParamRef(_): @unchecked)

    final def lookupRef(name: ThisName): Option[ParamRefType] =
      paramNames.indexOf(name) match
        case -1    => None
        case index => Some(paramRefs(index))

    def companion: LambdaTypeCompanion[ThisName, PInfo, This]

    /** The type `[params := this.paramRefs] tp`, where `params` can be
      * either a list of type parameter symbols or a list of lambda parameters
      */
    private[tastyquery] def integrate(params: List[Symbol], tp: Type): Type =
      Substituters.substLocalParams(tp, params, paramRefs)

    private[tastyquery] final def derivedLambdaType(
      paramNames: List[ThisName] = this.paramNames,
      paramInfos: List[PInfo] = this.paramInfos,
      resType: Type = this.resultType
    ): This =
      if (paramNames eq this.paramNames) && (paramInfos eq this.paramInfos) && (resType eq this.resultType) then
        this.asInstanceOf[This]
      else newLikeThis(paramNames, paramInfos, resType)

    private def newLikeThis(paramNames: List[ThisName], paramInfos: List[PInfo], resType: Type): This =
      companion(paramNames)(
        x => paramInfos.mapConserve(Substituters.substBinders(_, this, x).asInstanceOf[PInfo]),
        x => Substituters.substBinders(resType, this, x)
      )
  }

  sealed abstract class LambdaTypeCompanion[N <: Name, PInfo <: Type | TypeBounds, LT <: LambdaType] {
    def apply(paramNames: List[N])(paramInfosExp: LT => List[PInfo], resultTypeExp: LT => Type): LT

    final def apply(paramNames: List[N], paramInfos: List[PInfo], resultType: Type): LT =
      apply(paramNames)(_ => paramInfos, _ => resultType)
  }

  sealed abstract class TypeLambdaTypeCompanion[LT <: TypeLambdaType]
      extends LambdaTypeCompanion[TypeName, TypeBounds, LT] {
    @targetName("fromParamsSymbols")
    private[tastyquery] final def fromParams(params: List[LocalTypeParamSymbol], resultType: Type)(
      using Context
    ): Type =
      if params.isEmpty then resultType
      else
        val paramNames = params.map(_.name)
        val paramTypeBounds = params.map(_.bounds)
        apply(paramNames)(
          tpLambda => paramTypeBounds.map(tpLambda.integrate(params, _)),
          tpLambda => tpLambda.integrate(params, resultType)
        )
  }

  sealed trait TermLambdaType extends LambdaType:
    type ThisName = TermName
    type PInfo = Type
    type This <: TermLambdaType
    type ParamRefType = TermParamRef

    protected def newParamRef(n: Int): ParamRefType = TermParamRef(this, n)

    def paramTypes: List[Type]

    final def paramInfos: List[PInfo] =
      paramTypes

    final def instantiate(args: List[Type])(using Context): Type =
      Substituters.substParams(resultType, this, args)

    final def instantiateParamTypes(args: List[Type])(using Context): List[Type] =
      paramTypes.map(Substituters.substParams(_, this, args))
  end TermLambdaType

  sealed trait TypeLambdaType extends LambdaType with TypeBinders:
    type ThisName = TypeName
    type PInfo = TypeBounds
    type This <: TypeLambdaType
    type ParamRefType = TypeParamRef

    protected def newParamRef(n: Int): ParamRefType = TypeParamRef(this, n)

    def paramTypeBounds: List[TypeBounds]

    final def paramInfos: List[PInfo] =
      paramTypeBounds

    final def instantiate(args: List[Type])(using Context): Type =
      Substituters.substParams(resultType, this, args)

    final def instantiateParamTypeBounds(args: List[Type])(using Context): List[TypeBounds] =
      paramTypeBounds.map(Substituters.substParams(_, this, args))

    /** The type-bounds `[tparams := this.paramRefs] bounds`, where `tparams` is a list of type parameter symbols */
    private[tastyquery] def integrate(tparams: List[TypeParamSymbol], bounds: TypeBounds): TypeBounds =
      Substituters.substLocalParams(bounds, tparams, paramRefs)
  end TypeLambdaType

  final class MethodType(val paramNames: List[TermName])(
    @constructorOnly paramTypesExp: MethodType => List[Type],
    @constructorOnly resultTypeExp: MethodType => Type
  ) extends MethodicType
      with TermLambdaType:
    type This = MethodType

    private var initialized: Boolean = false
    private val myParamTypes: List[Type] = paramTypesExp(this: @unchecked)
    private val myRes: Type = resultTypeExp(this: @unchecked)
    initialized = true

    def paramTypes: List[Type] =
      if !initialized then throw CyclicReferenceException(s"method [$paramNames]=>???")
      myParamTypes.nn

    def resultType: Type =
      if !initialized then throw CyclicReferenceException(s"method [$paramNames]=>???")
      myRes.nn

    def companion: LambdaTypeCompanion[TermName, Type, MethodType] = MethodType

    private[tastyquery] def isResultDependent(using Context): Boolean =
      // TODO This should be made more efficient; we only need to traverse the type, not transform it
      object traverser extends TypeMaps.TypeMap:
        var isDependent: Boolean = false

        def apply(tp: Type): Type = tp match
          case _ if isDependent =>
            tp
          case tp: TermParamRef if tp.binders eq MethodType.this =>
            isDependent = true
            tp
          case _ =>
            mapOver(tp)
        end apply
      end traverser

      traverser(resultType)
      traverser.isDependent
    end isResultDependent

    private[tastyquery] def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult =
      throw new AssertionError(s"Cannot find member in $this")

    private[tastyquery] def resolveMatchingMember(name: SignedName, pre: Type, typePredicate: Type => Boolean)(
      using Context
    ): ResolveMemberResult =
      throw new AssertionError(s"Cannot find member in $this")

    override def toString: String =
      if !initialized then s"MethodType($paramNames)(<evaluating>...)"
      else s"MethodType($paramNames)($paramTypes, $resultType)"
  end MethodType

  object MethodType extends LambdaTypeCompanion[TermName, Type, MethodType]:
    def apply(
      paramNames: List[TermName]
    )(paramInfosExp: MethodType => List[Type], resultTypeExp: MethodType => Type): MethodType =
      new MethodType(paramNames)(paramInfosExp, resultTypeExp)

    /** Produce method type from parameter symbols, with special mappings for repeated
      *  and inline parameters:
      *   - replace @repeated annotations on Seq or Array types by <repeated> types
      *   - add @inlineParam to inline parameters
      */
    private[tastyquery] def fromSymbols(params: List[TermSymbol], resultType: Type)(using Context): MethodType = {
      def annotatedToRepeated(tpe: Type): Type = tpe match
        case tpe: AnnotatedType if tpe.annotation.safeIsInternalRepeatedAnnot =>
          tpe.typ match
            case applied: AppliedType if applied.args.sizeIs == 1 =>
              // We're going to assume that `tycon` is indeed `Seq`, here, because we cannot afford to resolve it
              defn.RepeatedTypeOf(applied.args.head)
            case _ =>
              throw TastyFormatException(s"in $params, $tpe is declared repeated but is not a Seq type")
        case _ =>
          tpe
      end annotatedToRepeated

      // def translateInline(tp: Type): Type =
      //   AnnotatedType(tp, Annotation(defn.InlineParamAnnot))
      // def translateErased(tp: Type): Type =
      //   AnnotatedType(tp, Annotation(defn.ErasedParamAnnot))
      def paramInfo(param: TermSymbol): Type = {
        var paramType = annotatedToRepeated(param.declaredType)
        // if (param.is(Inline)) paramType = translateInline(paramType)
        // if (param.is(Erased)) paramType = translateErased(paramType)
        paramType
      }

      MethodType(params.map(_.name.toTermName))(
        tl => params.map(p => tl.integrate(params, paramInfo(p))),
        tl => tl.integrate(params, resultType)
      )
    }

  final class PolyType private (val paramNames: List[TypeName])(
    @constructorOnly paramTypeBoundsExp: PolyType => List[TypeBounds],
    @constructorOnly resultTypeExp: PolyType => Type
  ) extends MethodicType
      with Binders
      with TypeLambdaType {
    type This = PolyType

    private var initialized: Boolean = false
    private val myBounds: List[TypeBounds] = paramTypeBoundsExp(this: @unchecked)
    private val myRes: Type = resultTypeExp(this: @unchecked)
    initialized = true

    def paramTypeBounds: List[TypeBounds] =
      if !initialized then throw CyclicReferenceException(s"polymorphic method [$paramNames]=>???")
      myBounds.nn

    def resultType: Type =
      if !initialized then throw CyclicReferenceException(s"polymorphic method [$paramNames]=>???")
      myRes.nn

    def companion: LambdaTypeCompanion[TypeName, TypeBounds, PolyType] =
      PolyType

    private[tastyquery] def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult =
      throw new AssertionError(s"Cannot find member in $this")

    private[tastyquery] def resolveMatchingMember(name: SignedName, pre: Type, typePredicate: Type => Boolean)(
      using Context
    ): ResolveMemberResult =
      throw new AssertionError(s"Cannot find member in $this")

    override def toString: String =
      if !initialized then s"PolyType($paramNames)(<evaluating>...)"
      else s"PolyType($paramNames)($myBounds, $myRes)"
  }

  object PolyType extends TypeLambdaTypeCompanion[PolyType]:
    def apply(
      paramNames: List[TypeName]
    )(paramTypeBoundsExp: PolyType => List[TypeBounds], resultTypeExp: PolyType => Type): PolyType =
      new PolyType(paramNames)(paramTypeBoundsExp, resultTypeExp)

    private[tastyquery] def fromParams(params: List[TypeParam], resultType: Type)(using Context): Type =
      if params.isEmpty then resultType
      else
        val paramNames = params.map(_.name)
        val paramSyms = params.map(_.symbol)
        apply(paramNames)(
          polyType => paramSyms.map(param => polyType.integrate(paramSyms, param.bounds)),
          polyType => polyType.integrate(paramSyms, resultType)
        )
  end PolyType

  /** Encapsulates the binders associated with a ParamRef. */
  sealed trait Binders

  sealed trait ParamRefBinders extends Binders:
    def paramRefs: List[ParamRef]

  sealed trait TypeBinders extends ParamRefBinders:
    def paramRefs: List[TypeParamRef]
    def lookupRef(name: TypeName): Option[Type]
    def paramNames: List[TypeName]
    def paramTypeBounds: List[TypeBounds]
  end TypeBinders

  sealed trait BoundType extends Type:
    type BindersType <: Binders
    def binders: BindersType
    private[tastyquery] def copyBoundType(newBinders: BindersType): Type

  sealed trait ParamRef extends BoundType:
    def paramNum: Int

  private[tastyquery] final class TypeLambdaParam(val typeLambda: TypeLambda, num: Int) extends TypeConstructorParam:
    def variance(using Context): Variance =
      Variance.Invariant // TODO Set structured variances

    def name: TypeName =
      typeLambda.paramNames(num)

    def bounds(using Context): TypeBounds =
      typeLambda.paramTypeBounds(num)
  end TypeLambdaParam

  final class TypeLambda(val paramNames: List[TypeName])(
    @constructorOnly paramTypeBoundsExp: TypeLambda => List[TypeBounds],
    @constructorOnly resultTypeExp: TypeLambda => Type
  ) extends TypeProxy
      with ValueType
      with TypeLambdaType {
    type This = TypeLambda

    private var initialized: Boolean = false
    private val myBounds: List[TypeBounds] = paramTypeBoundsExp(this: @unchecked)
    private val myRes: Type = resultTypeExp(this: @unchecked)
    initialized = true

    def paramTypeBounds: List[TypeBounds] =
      if !initialized then throw CyclicReferenceException(s"type lambda [$paramNames]=>???")
      myBounds.nn

    def resultType: Type =
      if !initialized then throw CyclicReferenceException(s"type lambda [$paramNames]=>???")
      myRes.nn

    private[tastyquery] lazy val typeLambdaParams: List[TypeLambdaParam] =
      List.tabulate(paramNames.size)(num => TypeLambdaParam(this, num))

    def companion: LambdaTypeCompanion[TypeName, TypeBounds, TypeLambda] = TypeLambda

    override def underlying(using Context): Type = defn.AnyType

    override def toString: String =
      if !initialized then s"TypeLambda($paramNames)(<evaluating>)"
      else s"TypeLambda($paramNames)($myBounds, $myRes)"
  }

  object TypeLambda extends TypeLambdaTypeCompanion[TypeLambda]:
    def apply(
      paramNames: List[TypeName]
    )(paramInfosExp: TypeLambda => List[TypeBounds], resultTypeExp: TypeLambda => Type): TypeLambda =
      new TypeLambda(paramNames)(paramInfosExp, resultTypeExp)

    private[tastyquery] def fromParams(params: List[TypeParam])(resultTypeExp: TypeLambda => Type)(
      using Context
    ): TypeLambda =
      apply(params.map(_.name))(_ => params.map(_.symbol.bounds), resultTypeExp)

    private[tastyquery] def fromParamInfos(params: List[TypeConstructorParam])(resultTypeExp: TypeLambda => Type)(
      using Context
    ): TypeLambda =
      apply(params.map(_.name))(_ => params.map(_.bounds), resultTypeExp)
  end TypeLambda

  final class TypeParamRef(val binders: TypeBinders, val paramNum: Int) extends TypeProxy with ValueType with ParamRef {
    type BindersType = TypeBinders

    private[tastyquery] def copyBoundType(newBinders: BindersType): Type =
      newBinders.paramRefs(paramNum)

    override def underlying(using Context): Type = bounds.high

    def paramName: TypeName = binders.paramNames(paramNum)

    def bounds(using Context): TypeBounds = binders.paramTypeBounds(paramNum)

    override def toString: String = paramName.toString
  }

  final class TermParamRef(val binders: TermLambdaType, val paramNum: Int) extends ParamRef with SingletonType {
    type BindersType = TermLambdaType

    private[tastyquery] def copyBoundType(newBinders: BindersType): Type =
      newBinders.paramRefs(paramNum)

    def underlying(using Context): Type = binders.paramInfos(paramNum)

    final def paramName: TermName = binders.paramNames(paramNum)

    override def toString(): String = paramName.toString
  }

  /** typ @ annot */
  final class AnnotatedType(val typ: Type, val annotation: Annotation) extends TypeProxy with ValueType {
    override def underlying(using Context): Type = typ

    private[tastyquery] final def derivedAnnotatedType(typ: Type, annotation: Annotation): AnnotatedType =
      if ((typ eq this.typ) && (annotation eq this.annotation)) this
      else AnnotatedType(typ, annotation)

    override def toString(): String = s"AnnotatedType($typ, $annotation)"
  }

  sealed abstract class RefinedOrRecType extends TypeProxy with ValueType

  sealed abstract class RefinedType extends RefinedOrRecType:
    val parent: Type
    val refinedName: Name

    override final def underlying(using Context): Type = parent
  end RefinedType

  /** A type refinement `parent { type refinedName <:> refinedBounds }`.
    * @param parent        The type being refined
    * @param refinedName   The name of the refined type member
    * @param refinedBounds The refined bounds for the given type member
    */
  final class TypeRefinement(val parent: Type, val refinedName: TypeName, val refinedBounds: TypeBounds)
      extends RefinedType:
    private[tastyquery] override def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult =
      val parentMember = parent.resolveMember(name, pre)

      if name != refinedName then parentMember
      else
        val myResult = ResolveMemberResult.TypeMember(Nil, refinedBounds)
        ResolveMemberResult.merge(parentMember, myResult)
    end resolveMember

    private[tastyquery] final def derivedTypeRefinement(
      parent: Type,
      refinedName: TypeName,
      refinedBounds: TypeBounds
    ): Type =
      if ((parent eq this.parent) && (refinedName eq this.refinedName) && (refinedBounds eq this.refinedBounds)) this
      else TypeRefinement(parent, refinedName, refinedBounds)
    end derivedTypeRefinement

    override def toString(): String = s"TypeRefinement($parent, $refinedName, $refinedBounds)"
  end TypeRefinement

  /** A term refinement `parent { val/def refinedName: refinedType }`.
    * @param parent      The type being refined
    * @param refinedName The name of the refined term member
    * @param refinedType The refined type for the given term member
    */
  final class TermRefinement(val parent: Type, val isStable: Boolean, val refinedName: TermName, val refinedType: Type)
      extends RefinedType:
    @deprecated("use the overload with an explicit isStable argument", since = "0.7.4")
    def this(parent: Type, refinedName: TermName, refinedType: Type) =
      this(parent, isStable = false, refinedName, refinedType)

    // Cache fields
    private[tastyquery] val isMethodic = refinedType.isInstanceOf[MethodicType]
    private var mySignedName: SignedName | Null = null

    require(!(isStable && isMethodic), s"Ill-formed $this")

    private[tastyquery] def signedName(using Context): SignedName =
      val local = mySignedName
      if local != null then local
      else
        val sig = Signature.fromType(refinedType, SourceLanguage.Scala3, optCtorReturn = None)
        val computed = SignedName(refinedName, sig)
        mySignedName = computed
        computed
    end signedName

    private[tastyquery] override def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult =
      if !isMethodic then
        val parentMember = parent.resolveMember(name, pre)
        if name != refinedName then parentMember
        else
          parentMember match
            case ResolveMemberResult.TermMember(symbols, tpe) =>
              ResolveMemberResult.TermMember(symbols, tpe & refinedType)
            case _ =>
              ResolveMemberResult.TermMember(Nil, refinedType)
      else
        name match
          case SignedName(simpleName, sig, _) if simpleName == refinedName && sig.paramsCorrespond(signedName.sig) =>
            val parentMember = parent.resolveMatchingMember(signedName, pre, refinedType.isSubtype(_))
            parentMember match
              case ResolveMemberResult.TermMember(symbols, _) =>
                // We can disregard the type coming from parent because we selected for `refinedType.isSubtype(_)`
                ResolveMemberResult.TermMember(symbols, refinedType)
              case _ =>
                ResolveMemberResult.TermMember(Nil, refinedType)
          case _ =>
            parent.resolveMember(name, pre)
    end resolveMember

    private[tastyquery] override def resolveMatchingMember(name: SignedName, pre: Type, typePredicate: Type => Boolean)(
      using Context
    ): ResolveMemberResult =
      if isMethodic && name.underlying == refinedName && name.sig.paramsCorrespond(signedName.sig) then
        if !typePredicate(refinedType) then ResolveMemberResult.NotFound
        else
          val parentMember = parent.resolveMatchingMember(signedName, pre, refinedType.isSubtype(_))
          parentMember match
            case ResolveMemberResult.TermMember(symbols, _) =>
              // We can disregard the type coming from parent because we selected for `refinedType.isSubtype(_)`
              ResolveMemberResult.TermMember(symbols, refinedType)
            case _ =>
              ResolveMemberResult.TermMember(Nil, refinedType)
      else parent.resolveMatchingMember(name, pre, typePredicate)
    end resolveMatchingMember

    private[tastyquery] final def derivedTermRefinement(parent: Type, refinedName: TermName, refinedType: Type): Type =
      if ((parent eq this.parent) && (refinedName eq this.refinedName) && (refinedType eq this.refinedType)) this
      else TermRefinement(parent, isStable, refinedName, refinedType)

    override def toString(): String = s"TermRefinement($parent, $refinedName, $refinedType)"
  end TermRefinement

  final class RecType private (parentExp: RecType => Type) extends RefinedOrRecType with Binders:
    private var initialized = false

    /** Reference to this recursive type from within itself. */
    val recThis: RecThis = RecThis(this)
    private val myParent: Type = parentExp(this: @unchecked)
    initialized = true

    def parent: Type =
      if !initialized then throw CyclicReferenceException("RecType(???)")
      myParent

    def underlying(using Context): Type = parent

    final def expand(recThisType: Type)(using Context): Type =
      Substituters.substRecThis(parent, this, recThisType)

    override def toString(): String = s"RecType@$debugID($parent)"

    def debugID: Int = System.identityHashCode(this)
  end RecType

  object RecType:
    def apply(parentExp: RecType => Type): RecType =
      new RecType(parentExp) // TODO? Perform normalization like dotc?
  end RecType

  final class RecThis(binder: RecType) extends BoundType with SingletonType:
    type BindersType = RecType

    final def binders: BindersType = binder

    final def copyBoundType(newBinder: RecType): Type = newBinder.recThis

    final def underlying(using Context): Type = binder

    override def toString(): String = s"RecThis(RecType@${binder.debugID})"
  end RecThis

  /** case `pattern` => `result` */
  final class MatchTypeCase(val paramNames: List[TypeName])(
    @constructorOnly paramTypeBoundsExp: MatchTypeCase => List[TypeBounds],
    @constructorOnly patternExp: MatchTypeCase => Type,
    @constructorOnly resultTypeExp: MatchTypeCase => Type
  ) extends TypeBinders:
    val paramRefs: List[TypeParamRef] =
      List.tabulate(paramNames.size)(i => TypeParamRef(this: @unchecked, i))

    private var initialized: Boolean = false
    private val myParamTypeBounds: List[TypeBounds] = paramTypeBoundsExp(this: @unchecked)
    private val myPattern: Type = patternExp(this: @unchecked)
    private val myResult: Type = resultTypeExp(this: @unchecked)
    initialized = true

    def paramTypeBounds: List[TypeBounds] =
      if !initialized then throw CyclicReferenceException(s"match [$paramNames]=>???")
      myParamTypeBounds.nn

    def pattern: Type =
      if !initialized then throw CyclicReferenceException(s"match [$paramNames]=>???")
      myPattern.nn

    def result: Type =
      if !initialized then throw CyclicReferenceException(s"match [$paramNames]=>???")
      myResult.nn

    final def lookupRef(name: TypeName): Option[TypeParamRef] =
      paramNames.indexOf(name) match
        case -1    => None
        case index => Some(paramRefs(index))

    /** The type `[params := this.paramRefs] tp`. */
    private def integrate(params: List[Symbol], tp: Type): Type =
      Substituters.substLocalParams(tp, params, paramRefs)

    /** The type-bounds `[tparams := this.paramRefs] bounds`. */
    private def integrate(tparams: List[TypeParamSymbol], bounds: TypeBounds): TypeBounds =
      Substituters.substLocalParams(bounds, tparams, paramRefs)

    private[tastyquery] def derivedMatchTypeCase(
      paramTypeBounds: List[TypeBounds],
      pattern: Type,
      result: Type
    ): MatchTypeCase =
      if (paramTypeBounds eq this.paramTypeBounds) && (pattern eq this.pattern) && (result eq this.result) then this
      else
        MatchTypeCase(paramNames)(
          x => paramTypeBounds.mapConserve(Substituters.substBinders(_, this, x)),
          x => Substituters.substBinders(pattern, this, x),
          x => Substituters.substBinders(result, this, x)
        )
    end derivedMatchTypeCase

    override def toString(): String =
      if !initialized then s"MatchTypeCase($paramNames)(<evaluating>)"
      else s"MatchTypeCase($paramNames)($paramTypeBounds, $pattern, $result)"
  end MatchTypeCase

  object MatchTypeCase:
    def apply(paramNames: List[TypeName])(
      paramTypeBoundsExp: MatchTypeCase => List[TypeBounds],
      patternExp: MatchTypeCase => Type,
      resultTypeExp: MatchTypeCase => Type
    ): MatchTypeCase =
      new MatchTypeCase(paramNames)(paramTypeBoundsExp, patternExp, resultTypeExp)
    end apply

    def apply(pattern: Type, result: Type): MatchTypeCase =
      new MatchTypeCase(Nil)(_ => Nil, _ => pattern, _ => result)

    private[tastyquery] final def fromParams(params: List[LocalTypeParamSymbol], pattern: Type, result: Type)(
      using Context
    ): MatchTypeCase =
      val paramNames = params.map(_.name)
      val paramTypeBounds = params.map(_.bounds)
      apply(paramNames)(
        mtc => paramTypeBounds.map(mtc.integrate(params, _)),
        mtc => mtc.integrate(params, pattern),
        mtc => mtc.integrate(params, result)
      )
  end MatchTypeCase

  /** selector match { cases } */
  final class MatchType(val bound: Type, val scrutinee: Type, val cases: List[MatchTypeCase])
      extends TypeProxy
      with ValueType:
    private var myReduced: Option[Type] | Null = null

    def underlying(using Context): Type = bound

    def reduced(using Context): Option[Type] =
      val local = myReduced
      if local != null then local
      else
        val computed = computeReduced()
        myReduced = computed
        computed
    end reduced

    private def computeReduced()(using Context): Option[Type] =
      TypeMatching.matchCases(scrutinee, cases)

    override def toString(): String = s"MatchType($bound, $scrutinee, $cases)"

    private[tastyquery] def derivedMatchType(bound: Type, scrutinee: Type, cases: List[MatchTypeCase]): MatchType =
      if (bound eq this.bound) && (scrutinee eq this.scrutinee) && (cases eq this.cases) then this
      else MatchType(bound, scrutinee, cases)
  end MatchType

  sealed abstract class TypeBounds(val low: Type, val high: Type) extends TypeMappable {
    type ThisTypeMappableType = TypeBounds

    /** The non-alias type bounds type with given bounds */
    private[tastyquery] def derivedTypeBounds(low: Type, high: Type): TypeBounds =
      if ((low eq this.low) && (high eq this.high)) this
      else RealTypeBounds(low, high)

    final def contains(tp: Type)(using Context): Boolean = tp match
      case tp: WildcardTypeBounds =>
        low.isSubtype(tp.bounds.low) && tp.bounds.high.isSubtype(high)
      case _ =>
        low.isSubtype(tp) && tp.isSubtype(high)
    end contains

    final def contains(that: TypeBounds)(using Context): Boolean =
      this.low.isSubtype(that.low) && that.high.isSubtype(this.high)

    final def intersect(that: TypeBounds)(using Context): TypeBounds =
      if this.contains(that) then that
      else if that.contains(this) then this
      else RealTypeBounds(this.low | that.low, this.high & that.high)

    final def union(that: TypeBounds)(using Context): TypeBounds =
      if this.contains(that) then this
      else if that.contains(this) then that
      else RealTypeBounds(this.low & that.low, this.high | that.high)

    private[tastyquery] def mapBounds(f: Type => Type): TypeBounds = this match
      case RealTypeBounds(low, high) => derivedTypeBounds(f(low), f(high))
      case self @ TypeAlias(alias)   => self.derivedTypeAlias(f(alias))
    end mapBounds
  }

  final case class RealTypeBounds(override val low: Type, override val high: Type) extends TypeBounds(low, high):
    override def toString(): String = s"TypeBounds($low, $high)"
  end RealTypeBounds

  final case class TypeAlias(alias: Type) extends TypeBounds(alias, alias) {
    private[tastyquery] def derivedTypeAlias(alias: Type): TypeAlias =
      if alias eq this.alias then this
      else TypeAlias(alias)

    override def toString(): String = s"TypeAlias($alias)"
  }

  /** A skolem type reference with underlying type `tpe`.
    *
    * For tasty-query, a skolem type is a singleton type of some unknown value
    * of type `tpe`.
    *
    * Skolem types do not appear as the types of trees or symbols, but they
    * may be used internally, notably for subtyping and member lookup purposes.
    *
    * Note that care is needed when creating them, since not all types need to
    * be inhabited.
    *
    * A skolem is equal to itself and no other type.
    */
  final class SkolemType(val tpe: Type) extends SingletonType {
    override def underlying(using Context): Type = tpe

    private[tastyquery] def derivedSkolemType(tpe: Type)(using Context): SkolemType =
      if (tpe eq this.tpe) this else SkolemType(tpe)

    override def toString: String = s"SkolemType@$debugID($tpe)"

    def debugID: Int = System.identityHashCode(this)
  }

  final class WildcardTypeBounds(val bounds: TypeBounds) extends TypeProxy {
    override def underlying(using Context): Type = bounds.high

    private[tastyquery] def derivedWildcardTypeBounds(bounds: TypeBounds): WildcardTypeBounds =
      if bounds eq this.bounds then this
      else WildcardTypeBounds(bounds)

    override def toString(): String = s"WildcardTypeBounds($bounds)"
  }

  object WildcardTypeBounds:
    def NothingAny(using Context): WildcardTypeBounds =
      WildcardTypeBounds(defn.NothingAnyBounds)
  end WildcardTypeBounds

  // ----- Ground Types -------------------------------------------------

  final class OrType(val first: Type, val second: Type) extends GroundType with ValueType {
    private var myJoin: Type | Null = uninitialized

    /** Returns the closest non-OrType type above this one. */
    def join(using Context): Type = {
      val myJoin = this.myJoin
      if (myJoin != null) then myJoin
      else
        val computedJoin = defn.ObjectType // TypeOps.orDominator(this)
        this.myJoin = computedJoin
        computedJoin
    }

    private[tastyquery] def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult =
      join.resolveMember(name, pre)

    private[tastyquery] def resolveMatchingMember(name: SignedName, pre: Type, typePredicate: Type => Boolean)(
      using Context
    ): ResolveMemberResult =
      join.resolveMatchingMember(name, pre, typePredicate)

    private[tastyquery] def derivedOrType(first: Type, second: Type): Type =
      if (first eq this.first) && (second eq this.second) then this
      else OrType.make(first, second)

    override def toString(): String = s"OrType($first, $second)"
  }

  object OrType {
    private[tastyquery] def make(first: Type, second: Type): Type =
      if (first eq second) first
      else OrType(first, second)
  }

  final class AndType(val first: Type, val second: Type) extends GroundType with ValueType {
    private[tastyquery] def resolveMember(name: Name, pre: Type)(using Context): ResolveMemberResult =
      ResolveMemberResult.merge(first.resolveMember(name, pre), second.resolveMember(name, pre))

    private[tastyquery] def resolveMatchingMember(name: SignedName, pre: Type, typePredicate: Type => Boolean)(
      using Context
    ): ResolveMemberResult =
      ResolveMemberResult.merge(
        first.resolveMatchingMember(name, pre, typePredicate),
        second.resolveMatchingMember(name, pre, typePredicate)
      )
    end resolveMatchingMember

    private[tastyquery] def derivedAndType(first: Type, second: Type): Type =
      if ((first eq this.first) && (second eq this.second)) this
      else AndType.make(first, second)

    private[tastyquery] def parts: List[Type] =
      def rec(tpe: Type, acc: mutable.ListBuffer[Type]): acc.type = tpe match
        case tpe: AndType => rec(tpe.second, rec(tpe.first, acc))
        case tpe: Type    => acc += tpe
      rec(this, mutable.ListBuffer.empty).toList

    override def toString(): String = s"AndType($first, $second)"
  }

  object AndType {
    private[tastyquery] def make(first: Type, second: Type): Type =
      // TODO Avoid &'ing with Any
      if first eq second then first
      else AndType(first, second)

    private[tastyquery] def combineGlb(bt1: Option[Type], bt2: Option[Type])(using Context): Option[Type] =
      if bt1.isEmpty then bt2
      else if bt2.isEmpty then bt1
      else Some(bt1.get & bt2.get)
  }
}
