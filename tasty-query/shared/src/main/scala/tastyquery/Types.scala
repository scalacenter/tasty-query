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
  private[tastyquery] final case class LookupIn(pre: TypeRef, sel: SignedName)

  private[tastyquery] final case class Scala2ExternalSymRef(owner: Symbol, path: List[Name]) {
    val name = path.last
  }

  enum ErasedTypeRef:
    case ClassRef(cls: ClassSymbol)
    case ArrayTypeRef(base: ClassRef, dimensions: Int)

    def toDebugString: String = this match
      case ClassRef(cls)                  => s"ClassRef(${cls.erasedName.toDebugString})"
      case ArrayTypeRef(base, dimensions) => s"ArrayTypeRef(${base.toDebugString}, $dimensions)"

    override def toString(): String = this match
      case ClassRef(cls)                  => cls.erasedName.toString()
      case ArrayTypeRef(base, dimensions) => base.toString() + "[]" * dimensions

    def arrayOf(): ArrayTypeRef = this match
      case classRef: ClassRef             => ArrayTypeRef(classRef, 1)
      case ArrayTypeRef(base, dimensions) => ArrayTypeRef(base, dimensions + 1)

    /** The `FullyQualifiedName` for this `ErasedTypeRef` as found in the `TermSig`s of `Signature`s. */
    def toSigFullName: FullyQualifiedName = this match
      case ClassRef(cls) =>
        cls.erasedName

      case ArrayTypeRef(base, dimensions) =>
        val suffix = "[]" * dimensions
        val baseName = base.cls.erasedName
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
    def erase(tpe: Type)(using Context): ErasedTypeRef =
      Erasure.erase(tpe)
  end ErasedTypeRef

  /** A common super trait of Symbol and LambdaParam.
    * Used to capture the attributes of type parameters which can be implemented as either.
    */
  private[tastyquery] trait TypeParamInfo:
    /** The variance of the type parameter */
    private[tastyquery] def paramVariance(using Context): Variance
  end TypeParamInfo

  sealed trait TypeMappable:
    type ThisTypeMappableType >: this.type <: TypeMappable
  end TypeMappable

  sealed abstract class Prefix extends TypeMappable:
    type ThisTypeMappableType >: this.type <: Prefix

    final def memberType(member: TermSymbol)(using Context): Type =
      member.declaredType.asSeenFrom(this, member.owner)

    final def memberTypeBoundsLow(member: TypeSymbolWithBounds)(using Context): Type =
      member.lowerBound.asSeenFrom(this, member.owner)

    final def memberTypeBoundsHigh(member: TypeSymbolWithBounds)(using Context): Type =
      member.upperBound.asSeenFrom(this, member.owner)

    final def select(sym: TermOrTypeSymbol)(using Context): NamedType =
      NamedType(this, sym) // dotc also calls reduceProjection here, should we do it?

    /** True iff `sym` is a symbol of a class type parameter and the reference
      * `<pre> . <sym>` is an actual argument reference, i.e., `pre` is not the
      * ThisType of `sym`'s owner, or a reference to `sym`'s owner.'
      */
    private[tastyquery] final def isArgPrefixOf(sym: Symbol)(using Context): Boolean =
      sym match
        case sym: ClassTypeParamSymbol =>
          this match
            case tp: ThisType => tp.cls != sym.owner
            case tp: TypeRef  => tp.symbol != sym.owner
            case _            => true
        case _ =>
          false
    end isArgPrefixOf
  end Prefix

  object NoPrefix extends Prefix:
    type ThisTypeMappableType = this.type

    override def toString(): String = "NoPrefix"
  end NoPrefix

  sealed abstract class Type extends Prefix {
    type ThisTypeMappableType = Type

    final def isSubtype(that: Type)(using Context): Boolean =
      Subtyping.isSubtype(this, that)

    final def isSameType(that: Type)(using Context): Boolean =
      Subtyping.isSameType(this, that)

    /** The class symbol of this type, None if reduction is not possible */
    private[tastyquery] final def classSymbol(using Context): Option[ClassSymbol] = this.widen match
      case tpe: TypeRef =>
        tpe.symbol match
          case cls: ClassSymbol =>
            Some(cls)
          case typeSym: TypeMemberSymbol =>
            typeSym.typeDef match
              case TypeMemberDefinition.TypeAlias(alias) => alias.classSymbol
              case _                                     => None
          case _: TypeParamSymbol => None
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

    /** The type parameters of this type are:
      * For a ClassInfo type, the type parameters of its class.
      * For a typeref referring to a class, the type parameters of the class.
      * For a refinement type, the type parameters of its parent, dropping
      * any type parameter that is-rebound by the refinement.
      *
      * For any *-kinded type, returns `Nil`.
      */
    private[tastyquery] final def typeParams(using Context): List[TypeParamInfo] =
      this match
        case self: TypeRef =>
          self.symbol match
            case cls: ClassSymbol              => cls.typeParams
            case typeSym: TypeSymbolWithBounds => typeSym.upperBound.typeParams
        case self: TypeLambda =>
          self.typeLambdaParams
        case self: AppliedType =>
          self.tycon match
            case tycon: TypeRef if tycon.symbol.isClass => Nil
            case _                                      => self.superType.typeParams
        case _: SingletonType | _: RefinedType =>
          Nil
        case self: WildcardTypeBounds =>
          self.bounds.high.typeParams
        case self: TypeProxy =>
          self.superType.typeParams
        case _ =>
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
        tp.symbol match
          case tpSym: TypeMemberSymbol =>
            tpSym.typeDef match
              case TypeMemberDefinition.TypeAlias(alias)                          => alias.dealias1(keepOpaques)
              case TypeMemberDefinition.OpaqueTypeAlias(_, alias) if !keepOpaques => alias.dealias1(keepOpaques)
              case _                                                              => tp
          case _ =>
            tp
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
        tp.symbol match
          case sym: TypeMemberSymbol =>
            sym.typeDef match
              case TypeMemberDefinition.TypeAlias(alias) => alias.normalizedPrefix
              case _                                     => Some(tp.prefix)
          case _ =>
            Some(tp.prefix)
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

    /** The member with the given `name`. */
    private[tastyquery] final def member(name: Name)(using Context): Symbol =
      // We need a valid prefix for `asSeenFrom`
      findMember(name, widenIfUnstable).getOrElse {
        throw MemberNotFoundException(this, name)
      }

    /** Find the member of this type with the given `name` when prefix `pre`. */
    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Option[Symbol]

    private[Types] def lookupRefined(name: Name)(using Context): Option[Type] =
      None // TODO

    final def asSeenFrom(pre: Prefix, cls: Symbol)(using Context): Type =
      TypeOps.asSeenFrom(this, pre, cls)

    final def isRef(sym: Symbol)(using Context): Boolean =
      this match {
        case tpe: NamedType    => tpe.symbol == sym
        case tpe: AppliedType  => tpe.underlying.isRef(sym)
        case tpe: TermParamRef => tpe.underlying.isRef(sym)
        case tpe: TypeParamRef => tpe.bounds.high.isRef(sym)
        case _                 => false // todo: add ProxyType (need to fill in implementations of underlying)
      }

    /** Is this type exactly Nothing (no vars, aliases, refinements etc allowed)? */
    final def isExactlyNothing(using Context): Boolean = this match
      case tp: TypeRef =>
        tp.name == tpnme.Nothing && (tp.symbol eq defn.NothingClass)
      case _ =>
        false

    final def isOfClass(sym: Symbol)(using Context): Boolean =
      this match {
        case tpe: TermRef =>
          tpe.underlying.isOfClass(sym)
        case tpe: ConstantType =>
          tpe.underlying.isOfClass(sym)
        case _ =>
          this.isRef(sym)
      }

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
      case self: TypeRef =>
        self.symbol match
          case sym: ClassSymbol =>
            sym == defn.AnyKindClass || sym.typeParams.nonEmpty
          case sym: TypeSymbolWithBounds =>
            sym.upperBound.isLambdaSub
      case self: AppliedType =>
        self.tycon match
          case tycon: TypeRef if tycon.symbol.isClass => false
          case _                                      => self.superType.isLambdaSub
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

    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Option[Symbol] =
      underlying.findMember(name, pre)
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
    private[tastyquery] final def findMember(name: Name, pre: Type)(using Context): Option[Symbol] =
      throw AssertionError(s"Trying to findMember($name, $pre) on $this")
  end CustomTransientGroundType

  // ----- Marker traits ------------------------------------------------

  /** A marker trait for types that apply only to term symbols or that
    * represent higher-kinded types.
    */
  sealed trait TermType extends Type

  sealed trait MethodicType extends TermType

  /** A marker trait for types that can be types of values or that are higher-kinded */
  sealed trait ValueType extends TermType

  /** A marker trait for types that are guaranteed to contain only a
    * single non-null value (they might contain null in addition).
    */
  sealed trait SingletonType extends TypeProxy with ValueType

  sealed trait PathType extends TypeProxy with ValueType

  // ----- Type Proxies -------------------------------------------------

  sealed abstract class NamedType extends PathType {
    self =>

    type ThisName <: Name
    type ThisSymbolType <: TermOrTypeSymbol { type ThisNameType = ThisName }
    type ThisNamedType >: this.type <: NamedType
    protected type ThisDesignatorType >: ThisSymbolType <: TermOrTypeSymbol | Name | LookupIn | Scala2ExternalSymRef

    val prefix: Prefix

    protected def designator: ThisDesignatorType

    protected def storeComputedSymbol(sym: ThisSymbolType): Unit

    // For tests
    private[tastyquery] final def designatorInternal: TermOrTypeSymbol | Name | LookupIn | Scala2ExternalSymRef =
      designator

    private var myName: ThisName | Null = null
    private var mySymbol: ThisSymbolType | Null = null

    private[tastyquery] final def isLocalRef(sym: Symbol): Boolean =
      prefix == NoPrefix && designator == sym

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
      case LookupIn(_, sel)                 => sel
      case designator: Scala2ExternalSymRef => designator.name
    }).asInstanceOf[ThisName]

    final def symbol(using Context): ThisSymbolType =
      val local = mySymbol
      if local != null then local.asInstanceOf[ThisSymbolType] // Cast needed for expression evaluator
      else
        val computed = asThisSymbolType(computeSymbol())
        mySymbol = computed
        storeComputedSymbol(computed)
        computed

    protected def asThisSymbolType(sym: Symbol): ThisSymbolType

    private def computeSymbol()(using Context): Symbol = designator match
      case sym: TermOrTypeSymbol =>
        sym
      case LookupIn(pre, name) =>
        pre.member(name)
      case Scala2ExternalSymRef(owner, path) =>
        path.foldLeft(owner) { (owner, name) =>
          /* In Scala 2 external references, (term) *modules* can appear in paths.
           * When we find one, in our system, we must follow through to their module class
           * instead. The `declaredType` will in that case always be a `TypeRef` to the
           * module class.
           * Terms cannot otherwise appear in paths.
           */
          val cls = if owner.isTerm then owner.asTerm.declaredType.asInstanceOf[TypeRef].symbol else owner
          cls.asDeclaringSymbol.getDecl(name).getOrElse {
            throw new MemberNotFoundException(owner, name)
          }
        }
      case name: Name =>
        prefix match
          case prefix: Type =>
            prefix.member(name)
          case NoPrefix =>
            throw new AssertionError(s"found reference by name $name without a prefix")
    end computeSymbol

    /** The argument corresponding to class type parameter `tparam` as seen from
      * prefix `pre`. Can produce a TypeBounds type if `widenAbstract` is true,
      * or prefix is an & or | type and parameter is non-variant.
      * Otherwise, a typebounds argument is dropped and the original type parameter
      * reference is returned.
      */
    private[tastyquery] final def argForParam(pre: Type, widenAbstract: Boolean = false)(using Context): Option[Type] =
      val tparam = symbol.asInstanceOf[ClassTypeParamSymbol]
      val cls = tparam.owner
      val base = pre.baseType(cls)
      base match {
        case Some(base: AppliedType) =>
          var tparams = cls.typeParams
          var args = base.args
          var idx = 0
          while (tparams.nonEmpty && args.nonEmpty) {
            if (tparams.head.eq(tparam))
              return Some(args.head match {
                case _: WildcardTypeBounds if !widenAbstract => TypeRef(pre, tparam)
                case arg                                     => arg
              })
            tparams = tparams.tail
            args = args.tail
            idx += 1
          }
          None
        /*case base: AndOrType =>
          var tp1 = argForParam(base.tp1)
          var tp2 = argForParam(base.tp2)
          val variance = tparam.paramVarianceSign
          if (isBounds(tp1) || isBounds(tp2) || variance == 0) {
            // compute argument as a type bounds instead of a point type
            tp1 = tp1.bounds
            tp2 = tp2.bounds
          }
          if (base.isAnd == variance >= 0) tp1 & tp2 else tp1 | tp2*/
        case _ =>
          /*if (pre.termSymbol.isPackage) argForParam(pre.select(nme.PACKAGE))
          else*/
          if (pre.isExactlyNothing) Some(pre)
          else None
      }
    end argForParam

    /** A selection of the same kind, but with potentially a different prefix.
      * The following normalization is performed for type selections T#A:
      *
      *    T#A --> B    if A is bound to an alias `= B` in T
      */
    private[tastyquery] final def normalizedDerivedSelect(prefix: Type)(using Context): Type =
      if (prefix eq this.prefix) this
      else if (prefix.isExactlyNothing) prefix
      else {
        if (isType) {
          val res =
            if (!symbol.isClass && symbol.isAllOf(ClassTypeParam)) argForParam(prefix)
            else prefix.lookupRefined(name)
          if (res.isDefined)
            return res.get
        }

        designator match
          case sym: TermSymbol =>
            val refinedSym = prefix.member(sym.signedName).asTerm
            TermRef(prefix, refinedSym)
          case sym: TypeMemberSymbol =>
            val refinedSym = prefix.member(sym.name).asType
            TypeRef(prefix, refinedSym)
          case sym: TypeSymbol =>
            TypeRef(prefix, sym)
          case desig =>
            withPrefix(prefix, cachedSymbol = null)
      }
    end normalizedDerivedSelect

    private[tastyquery] final def derivedSelect(prefix: Prefix): ThisNamedType =
      if prefix eq this.prefix then this
      else withPrefix(prefix)

    private final def withPrefix(prefix: Prefix): ThisNamedType =
      withPrefix(prefix, cachedSymbol = mySymbol)

    protected def withPrefix(prefix: Prefix, cachedSymbol: ThisSymbolType | Null): ThisNamedType
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
    private var mySignature: Signature | Null = null

    protected def designator: ThisDesignatorType = myDesignator

    protected def storeComputedSymbol(sym: ThisSymbolType): Unit =
      myDesignator = sym

    override def toString(): String =
      s"TermRef($prefix, $myDesignator)"

    protected def asThisSymbolType(sym: Symbol): ThisSymbolType =
      sym.asInstanceOf[TermSymbol]

    private var myUnderlying: Type | Null = null

    override def underlying(using ctx: Context): Type = {
      val myUnderlying = this.myUnderlying
      if myUnderlying != null then myUnderlying
      else
        val computedUnderlying = computeUnderlying
        this.myUnderlying = computedUnderlying
        computedUnderlying
    }

    private def computeUnderlying(using ctx: Context): Type = {
      val termSymbol = symbol
      termSymbol.declaredType.asSeenFrom(prefix, termSymbol.owner)
    }

    private[tastyquery] final def signature(using Context): Signature =
      val local = mySignature
      if local != null then local
      else
        val computed = symbol.signature
        mySignature = computed
        computed
    end signature

    private[tastyquery] override def findMember(name: Name, pre: Type)(using Context): Option[Symbol] =
      underlying match
        case mt: MethodType if mt.paramInfos.isEmpty /*&& symbol.is(StableRealizable)*/ =>
          mt.resultType.findMember(name, pre)
        case tp =>
          tp.findMember(name, pre)

    protected def withPrefix(prefix: Prefix, cachedSymbol: ThisSymbolType | Null): TermRef =
      new TermRef(prefix, if cachedSymbol != null then cachedSymbol else designator)
  }

  object TermRef:
    def apply(prefix: Type, name: TermName): TermRef = new TermRef(prefix, name)
    def apply(prefix: Prefix, symbol: TermSymbol): TermRef = new TermRef(prefix, symbol)

    private[tastyquery] def apply(prefix: Type, designator: LookupIn): TermRef = new TermRef(prefix, designator)

    private[tastyquery] def apply(prefix: Prefix, external: Scala2ExternalSymRef): TermRef =
      new TermRef(prefix, external)
  end TermRef

  final class PackageRef(val fullyQualifiedName: FullyQualifiedName) extends Type {
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

    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Option[Symbol] =
      symbol.getDecl(name).orElse {
        /* #179 For some very unfortunate reason, Scala 3 emits TypeRefs
         * whose prefix is a PackageRef but the name references something in a
         * *package object*. That goes contrary to TASTy's purpose of being a
         * fully-resolved thing. We have to work around it here.
         * This is very annoying because we have to load a bunch of things that
         * may not be necessary.
         */
        symbol.allPackageObjectDecls().iterator.flatMap(_.getDecl(name)).nextOption()
      }

    override def toString(): String = s"PackageRef($fullyQualifiedName)"
  }

  final class TypeRef private (
    val prefix: Prefix,
    private var myDesignator: TypeName | TypeSymbol | Scala2ExternalSymRef
  ) extends NamedType {

    type ThisName = TypeName
    type ThisSymbolType = TypeSymbol
    type ThisNamedType = TypeRef
    type ThisDesignatorType = TypeName | TypeSymbol | Scala2ExternalSymRef

    protected def designator: ThisDesignatorType = myDesignator

    protected def storeComputedSymbol(sym: ThisSymbolType): Unit =
      myDesignator = sym

    override def toString(): String =
      s"TypeRef($prefix, $myDesignator)"

    protected def asThisSymbolType(sym: Symbol): ThisSymbolType =
      sym.asInstanceOf[TypeSymbol]

    override def underlying(using Context): Type = symbol match
      case cls: ClassSymbol =>
        throw AssertionError(s"TypeRef $this has no `underlying` because it refers to a `ClassSymbol`")
      case sym: TypeSymbolWithBounds =>
        sym.upperBound

    override def translucentSuperType(using Context): Type = symbol match
      case sym: TypeMemberSymbol =>
        sym.typeDef match
          case TypeMemberDefinition.OpaqueTypeAlias(_, alias) => alias
          case _                                              => underlying
      case _ =>
        underlying
    end translucentSuperType

    private[tastyquery] override def findMember(name: Name, pre: Type)(using Context): Option[Symbol] =
      symbol match
        case sym: ClassSymbol =>
          sym.findMember(pre, name)
        case sym: TypeSymbolWithBounds =>
          sym.upperBound.findMember(name, pre)

    protected def withPrefix(prefix: Prefix, cachedSymbol: ThisSymbolType | Null): TypeRef =
      new TypeRef(prefix, if cachedSymbol != null then cachedSymbol else designator)
  }

  object TypeRef:
    def apply(prefix: Type, name: TypeName): TypeRef = new TypeRef(prefix, name)
    def apply(prefix: Prefix, symbol: TypeSymbol): TypeRef = new TypeRef(prefix, symbol)

    private[tastyquery] def apply(prefix: Prefix, external: Scala2ExternalSymRef): TypeRef =
      new TypeRef(prefix, external)

    private[tastyquery] object OfClass:
      def unapply(typeRef: TypeRef)(using Context): Option[ClassSymbol] =
        val symbol = typeRef.symbol
        if symbol.isClass then Some(symbol.asClass)
        else None
    end OfClass
  end TypeRef

  final class ThisType(val tref: TypeRef) extends PathType with SingletonType {
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

    final def cls(using Context): ClassSymbol = tref.symbol.asClass

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
        case supertpe: TypeRef => supertpe.symbol.asClass
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
        case tycon: TypeRef if tycon.symbol.isClass => tycon
        case tycon: TypeProxy                       => tycon.superType.applyIfParameterized(args)
        case _                                      => defn.AnyType

    override def translucentSuperType(using Context): Type = tycon match
      case tycon: TypeRef if tycon.symbol.isOpaqueTypeAlias =>
        tycon.translucentSuperType.applyIfParameterized(args)
      case _ =>
        // tryNormalize.orElse(superType) // TODO for match types
        superType

    private[tastyquery] def tyconTypeParams(using Context): List[TypeParamInfo] =
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

    private[tastyquery] override def findMember(name: Name, pre: Type)(using Context): Option[Symbol] =
      tycon match
        case tycon: TypeRef =>
          if tycon.symbol.isClass then tycon.findMember(name, pre)
          else ???
        case _ =>
          ???

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
  end TermLambdaType

  sealed trait TypeLambdaType extends LambdaType with TypeBinders:
    type ThisName = TypeName
    type PInfo = TypeBounds
    type This <: TypeLambdaType
    type ParamRefType = TypeParamRef

    protected def newParamRef(n: Int): ParamRefType = TypeParamRef(this, n)

    def instantiate(args: List[Type])(using Context): Type =
      Substituters.substParams(resultType, this, args)

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

    def instantiate(args: List[Type])(using Context): Type =
      Substituters.substParams(resultType, this, args)

    def paramTypes: List[Type] =
      if !initialized then throw CyclicReferenceException(s"method [$paramNames]=>???")
      myParamTypes.nn

    def resultType: Type =
      if !initialized then throw CyclicReferenceException(s"method [$paramNames]=>???")
      myRes.nn

    def paramInfos: List[PInfo] =
      paramTypes

    def companion: LambdaTypeCompanion[TermName, Type, MethodType] = MethodType

    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Option[Symbol] =
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
      // def translateInline(tp: Type): Type =
      //   AnnotatedType(tp, Annotation(defn.InlineParamAnnot))
      // def translateErased(tp: Type): Type =
      //   AnnotatedType(tp, Annotation(defn.ErasedParamAnnot))
      def paramInfo(param: TermSymbol) = {
        var paramType = param.declaredType //.annotatedToRepeated
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

    def paramInfos: List[PInfo] = paramTypeBounds

    def companion: LambdaTypeCompanion[TypeName, TypeBounds, PolyType] =
      PolyType

    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Option[Symbol] =
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

  sealed trait BoundType extends Type:
    type BindersType <: Binders
    def binders: BindersType
    private[tastyquery] def copyBoundType(newBinders: BindersType): Type

  sealed trait ParamRef extends BoundType:
    def paramNum: Int

  private[tastyquery] final class TypeLambdaParam(val typeLambda: TypeLambda, num: Int) extends TypeParamInfo:
    override def paramVariance(using Context): Variance =
      Variance.Invariant // TODO? Should we set structure variances?
  end TypeLambdaParam

  final class TypeLambda(val paramNames: List[TypeName])(
    @constructorOnly paramTypeBoundsExp: TypeLambda => List[TypeBounds],
    @constructorOnly resultTypeExp: TypeLambda => Type
  ) extends TypeProxy
      with TermType
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

    def paramInfos: List[PInfo] = paramTypeBounds

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
  end TypeLambda

  final class TypeParamRef(val binders: TypeLambdaType, val paramNum: Int)
      extends TypeProxy
      with ValueType
      with ParamRef {
    type BindersType = TypeLambdaType

    private[tastyquery] def copyBoundType(newBinders: BindersType): Type =
      newBinders.paramRefs(paramNum)

    override def underlying(using Context): Type = bounds.high

    def paramName: TypeName = binders.paramNames(paramNum)

    def bounds(using Context): TypeBounds = binders.paramInfos(paramNum)

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

  sealed abstract class RefinedOrRecType extends TypeProxy

  sealed abstract class RefinedType extends RefinedOrRecType with ValueType:
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
  final class TermRefinement(val parent: Type, val refinedName: TermName, val refinedType: Type) extends RefinedType:
    private[tastyquery] final def derivedTermRefinement(parent: Type, refinedName: TermName, refinedType: Type): Type =
      if ((parent eq this.parent) && (refinedName eq this.refinedName) && (refinedType eq this.refinedType)) this
      else TermRefinement(parent, refinedName, refinedType)

    override def toString(): String = s"TermRefinement($parent, $refinedName, $refinedType)"
  end TermRefinement

  final class RecType private (parentExp: RecType => Type) extends RefinedOrRecType with Binders:
    val parent: Type = parentExp(this: @unchecked)

    /** Reference to this recursive type from within itself. */
    val recThis: RecThis = RecThis(this)

    def underlying(using Context): Type = parent
  end RecType

  object RecType:
    def apply(parentExp: RecType => Type): RecType =
      new RecType(parentExp) // TODO? Perform normalization like dotc?
  end RecType

  final class RecThis(binder: RecType) extends BoundType with SingletonType:
    type BindersType = RecType

    final def binders: BindersType = binder

    final def copyBoundType(newBinder: RecType): Type = RecThis(newBinder)

    final def underlying(using Context): Type = binder

    override def toString(): String = s"RecThis(<recursive>)"
  end RecThis

  /** case `pattern` => `result` */
  final class MatchTypeCase(val pattern: Type, val result: Type) extends GroundType:
    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Option[Symbol] =
      throw AssertionError(s"MatchTypeCase.findMember($name, $pre)")

    override def toString(): String = s"MatchTypeCase($pattern, $result)"
  end MatchTypeCase

  /** selector match { cases } */
  final class MatchType(val bound: Type, val scrutinee: Type, val cases: List[MatchTypeCase | TypeLambda])
      extends TypeProxy
      with ValueType:
    def underlying(using Context): Type = bound
    override def toString(): String = s"MatchType($bound, $scrutinee, $cases)"
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

  final class WildcardTypeBounds(val bounds: TypeBounds) extends TypeProxy {
    override def underlying(using Context): Type = bounds.high

    private[tastyquery] def derivedWildcardTypeBounds(bounds: TypeBounds): WildcardTypeBounds =
      if bounds eq this.bounds then this
      else WildcardTypeBounds(bounds)

    override def toString(): String = s"WildcardTypeBounds($bounds)"
  }

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

    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Option[Symbol] =
      join.findMember(name, pre)

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
    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Option[Symbol] =
      (first.findMember(name, pre), second.findMember(name, pre)) match
        case (Some(left: TermOrTypeSymbol), Some(right: TermOrTypeSymbol)) =>
          // TODO We should `meet` the two selections, but for now, pick one
          if right.overrides(left) then Some(right)
          else Some(left)
        case (left, right) => left.orElse(right)
    end findMember

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
  }
}
