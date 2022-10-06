package tastyquery

import scala.annotation.tailrec

import scala.collection.mutable

import dotty.tools.tasty.TastyFormat.NameTags

import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Variances.*

import scala.annotation.targetName

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

  object ErasedTypeRef {
    // TODO: improve this to match dotty:
    // - use correct type erasure algorithm from Scala 3, with specialisations
    //   for Java types and Scala 2 types (i.e. varargs, value-classes)
    def erase(tpe: Type)(using Context): ErasedTypeRef =
      tpe match
        case _: ExprType => ClassRef(defn.Function0Class)
        case _           => finishErase(preErase(tpe))
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
          if tpe.tycon.isRef(defn.ArrayClass) then
            val List(targ) = tpe.args: @unchecked
            arrayOf(targ).arrayOf()
          else arrayOf(tpe.tycon)
        case tpe: TypeRef =>
          tpe.symbol match
            case cls: ClassSymbol     => ClassRef(cls).arrayOf()
            case sym: TypeParamSymbol => arrayOfBounds(sym.bounds)
            case sym: TypeMemberSymbol =>
              sym.typeDef match
                case TypeMemberDefinition.TypeAlias(alias)          => arrayOf(alias)
                case TypeMemberDefinition.AbstractType(bounds)      => arrayOfBounds(bounds)
                case TypeMemberDefinition.OpaqueTypeAlias(_, alias) => arrayOf(alias)
        case tpe: TypeParamRef       => arrayOfBounds(tpe.bounds)
        case tpe: WildcardTypeBounds => arrayOfBounds(tpe.bounds)
        case _ =>
          preErase(tpe).arrayOf()
      end arrayOf

      tpe.widen match
        case tpe: AppliedType =>
          if tpe.tycon.isRef(defn.ArrayClass) then
            val List(targ) = tpe.args: @unchecked
            arrayOf(targ)
          else
            tpe.tycon match
              case tycon: TypeRef if tycon.symbol.isClass =>
                // Fast path
                ClassRef(tycon.symbol.asClass)
              case _ =>
                preErase(tpe.translucentSuperType)
        case tpe: TypeRef =>
          tpe.symbol match
            case cls: ClassSymbol =>
              ClassRef(cls)
            case sym: TypeParamSymbol =>
              preErase(sym.upperBound)
            case sym: TypeMemberSymbol =>
              sym.typeDef match
                case TypeMemberDefinition.TypeAlias(alias)          => preErase(alias)
                case TypeMemberDefinition.AbstractType(bounds)      => preErase(bounds.high)
                case TypeMemberDefinition.OpaqueTypeAlias(_, alias) => preErase(alias)
        case tpe: TypeParamRef =>
          preErase(tpe.bounds.high)
        case tpe: WildcardTypeBounds =>
          preErase(tpe.bounds.high)
        case tpe =>
          throw UnsupportedOperationException(s"Cannot erase $tpe")
    end preErase

    private def finishErase(typeRef: ErasedTypeRef)(using Context): ErasedTypeRef =
      def valueClass(cls: ClassSymbol): ErasedTypeRef =
        val ctor = cls.getDecl(nme.Constructor).get.asTerm
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
  }

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

  abstract class Type extends TypeMappable {
    type ThisTypeMappableType = Type

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
      case tpe: ThisType =>
        Some(tpe.cls)
      case info: ClassInfo =>
        Some(info.cls)
      case _ =>
        None

    /** The type parameters of this type are:
      * For a ClassInfo type, the type parameters of its class.
      * For a typeref referring to a class, the type parameters of the class.
      * For a refinement type, the type parameters of its parent, dropping
      * any type parameter that is-rebound by the refinement.
      *
      * For any *-kinded type, returns `Nil`.
      */
    private[Types] final def typeParams(using Context): List[TypeParamInfo] =
      this match
        case self: TypeRef =>
          self.symbol match
            case cls: ClassSymbol              => cls.typeParams
            case typeSym: TypeSymbolWithBounds => typeSym.upperBound.typeParams
        case self: AppliedType =>
          if (self.tycon.typeSymbol.isClass) Nil
          else self.superType.typeParams
        case self: ClassInfo =>
          self.cls.typeParams
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

    /** Substitute all types of the form `TypeParamRef(from, N)` by `TypeParamRef(to, N)`. */
    private[tastyquery] final def subst(from: Binders, to: Binders)(using Context): Type =
      Substituters.subst(this, from, to)

    /** Substitute bound types by some other types */
    private[tastyquery] final def substParams(from: Binders, to: List[Type])(using Context): Type =
      Substituters.substParams(this, from, to)

    private[tastyquery] final def typeSymbol(using Context): Symbol = this match
      case tpe: TypeRef => tpe.symbol
      case _            => NoSymbol

    private[tastyquery] final def termSymbol(using Context): Symbol = this match
      case tpe: TermRef => tpe.symbol
      case _            => NoSymbol

    private[tastyquery] final def widenOverloads(using Context): Type =
      this.widen match
        case tp: TermRef => tp.underlying.widenOverloads
        case tp          => tp

    /** Widen from ExprType type to its result type.
      *
      * For all other types, return `this`.
      */
    final def widenExpr: Type = this match {
      case tp: ExprType => tp.resultType
      case _            => this
    }

    /** Widen singleton types, ExprTypes, AnnotatedTypes and RefinedTypes. */
    final def widen(using Context): Type = this match
      case _: TypeRef | _: MethodType | _: PolyType => this // fast path for most frequent cases
      case tp: TermRef => // fast path for next most frequent case
        if tp.isOverloaded then tp else tp.underlying.widen
      case tp: SingletonType => tp.underlying.widen
      case tp: ExprType      => tp.resultType.widen
      case tp: AnnotatedType => tp.typ.widen
      case tp: RefinedType   => tp.parent.widen
      case tp                => tp

    private[tastyquery] final def widenIfUnstable(using Context): Type = this match
      // TODO Handle unstable term refs like method calls or values
      case tp: TermRef => tp
      case tp          => tp.widen

    final def dealias(using Context): Type = dealias1(keepOpaques = false)

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
      * - `NoType` for all other types.
      */
    @tailrec final def normalizedPrefix(using Context): Type = this match {
      case tp: TypeRef =>
        tp.symbol match
          case sym: TypeMemberSymbol =>
            sym.typeDef match
              case TypeMemberDefinition.TypeAlias(alias) => alias.normalizedPrefix
              case _                                     => tp.prefix
          case _ =>
            tp.prefix
      case tp: TermRef =>
        tp.prefix
      case tp: ClassInfo =>
        // TODO tp.prefix
        tp.cls.accessibleThisType
      case tp: TypeProxy =>
        tp.superType.normalizedPrefix
      case _ =>
        NoType
    }

    /** The basetype of this type with given class symbol, NoType if `base` is not a class. */
    final def baseType(base: Symbol)(using Context): Type =
      base match
        case base: ClassSymbol => base.baseTypeOf(this)
        case _                 => NoType

    /** The member with the given `name`. */
    final def member(name: Name)(using Context): Symbol =
      // We need a valid prefix for `asSeenFrom`
      val pre = this match
        case tp: ClassInfo => ??? // tp.appliedRef
        case _             => widenIfUnstable
      findMember(name, pre)

    /** Find the member of this type with the given `name` when prefix `pre`. */
    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Symbol

    private[Types] def lookupRefined(name: Name)(using Context): Type =
      NoType

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

    final def asSeenFrom(pre: Type, cls: Symbol)(using Context): Type =
      TypeOps.asSeenFrom(this, pre, cls)

    final def isRef(sym: Symbol)(using Context): Boolean =
      this match {
        case tpe: NamedType    => tpe.symbol == sym
        case tpe: AppliedType  => tpe.underlying.isRef(sym)
        case tpe: ExprType     => tpe.underlying.isRef(sym)
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
    private[tastyquery] final def isLambdaSub(using Context): Boolean = false // TODO hkResult.exists

    final def &(that: Type)(using Context): Type =
      // TypeComparer.glb(this, that)
      AndType.make(this, that)

    final def |(that: Type)(using Context): Type =
      // TypeCompare.lub(this, that)
      OrType.make(this, that)

    final def select(sym: Symbol)(using Context): Type =
      NamedType(this, sym) // dotc also calls reduceProjection here, should we do it?
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

    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Symbol =
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
  abstract class CustomTransientGroundType extends GroundType

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

  sealed trait PathType extends TypeProxy with ValueType {
    final def select(name: Name): NamedType = name match
      case name: TermName => TermRef(this, name)
      case name: TypeName => TypeRef(this, name)
  }

  // ----- Type Proxies -------------------------------------------------

  sealed abstract class NamedType extends PathType {
    self =>

    type ThisName <: Name
    type ThisSymbolType <: Symbol { type ThisNameType = ThisName }
    protected[this] type ThisDesignatorType >: ThisSymbolType <: Symbol | Name | LookupIn | Scala2ExternalSymRef

    val prefix: Type

    protected[this] def designator: ThisDesignatorType

    protected[this] def storeComputedSymbol(sym: ThisSymbolType): Unit

    // For tests
    private[tastyquery] final def designatorInternal: Symbol | Name | LookupIn | Scala2ExternalSymRef =
      designator

    private var myName: ThisName | Null = null
    private var mySymbol: ThisSymbolType | Null = null

    final def isType: Boolean = isInstanceOf[TypeRef]

    final def isTerm: Boolean = isInstanceOf[TermRef]

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
      case sym: Symbol                      => sym.name
      case LookupIn(_, sel)                 => sel
      case designator: Scala2ExternalSymRef => designator.name
    }).asInstanceOf[ThisName]

    final def selectIn(name: SignedName, in: TypeRef): TermRef =
      TermRef(this, LookupIn(in, name))

    final def symbol(using Context): ThisSymbolType =
      val local = mySymbol
      if local != null then local.asInstanceOf[ThisSymbolType] // Cast needed for expression evaluator
      else
        val computed = asThisSymbolType(computeSymbol())
        mySymbol = computed
        storeComputedSymbol(computed)
        computed

    protected[this] def asThisSymbolType(sym: Symbol): ThisSymbolType

    private def computeSymbol()(using Context): Symbol = designator match
      case sym: Symbol =>
        sym
      case LookupIn(pre, name) =>
        TermRef(pre, name).symbol
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
        if prefix == NoPrefix then
          throw new MemberNotFoundException(prefix, name, s"reference by name $name to a local symbol")
        prefix.member(name)
    end computeSymbol

    /** The argument corresponding to class type parameter `tparam` as seen from
      * prefix `pre`. Can produce a TypeBounds type if `widenAbstract` is true,
      * or prefix is an & or | type and parameter is non-variant.
      * Otherwise, a typebounds argument is dropped and the original type parameter
      * reference is returned.
      */
    private[tastyquery] final def argForParam(pre: Type, widenAbstract: Boolean = false)(using Context): Type = {
      val tparam = symbol.asInstanceOf[ClassTypeParamSymbol]
      val cls = tparam.owner
      val base = pre.baseType(cls)
      base match {
        case base: AppliedType =>
          var tparams = cls.typeParams
          var args = base.args
          var idx = 0
          while (tparams.nonEmpty && args.nonEmpty) {
            if (tparams.head.eq(tparam))
              return args.head match {
                case _: WildcardTypeBounds if !widenAbstract => TypeRef(pre, tparam)
                case arg                                     => arg
              }
            tparams = tparams.tail
            args = args.tail
            idx += 1
          }
          NoType
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
          if (pre.isExactlyNothing) pre
          else NoType
      }
    }

    /** A selection of the same kind, but with potentially a different prefix.
      * The following normalization is performed for type selections T#A:
      *
      *    T#A --> B    if A is bound to an alias `= B` in T
      */
    private[tastyquery] final def derivedSelect(prefix: Type)(using Context): Type =
      if (prefix eq this.prefix) this
      else if (prefix.isExactlyNothing) prefix
      else {
        if (isType) {
          val res =
            if (!symbol.isClass && symbol.isAllOf(ClassTypeParam)) argForParam(prefix)
            else prefix.lookupRefined(name)
          if (res != NoType)
            return res
        }
        /*if (prefix.isInstanceOf[WildcardType]) WildcardType
        else*/
        withPrefix(prefix, cachedSymbol = mySymbol)
      }

    protected[this] def withPrefix(prefix: Type, cachedSymbol: ThisSymbolType | Null)(using Context): Type
  }

  object NamedType {

    private[tastyquery] def possibleSelFromPackage(prefix: Type, name: TermName)(using Context): Type = prefix match
      case prefix: PackageRef if name.isInstanceOf[SimpleName] =>
        prefix.symbol.getPackageDeclInternal(name.asSimpleName) match
          case Some(nested) => PackageRef(nested)
          case _            => apply(prefix, name)
      case prefix =>
        apply(prefix, name)

    def apply(prefix: Type, sym: Symbol)(using Context): NamedType =
      sym match
        case sym: TypeSymbol => TypeRef(prefix, sym)
        case sym: TermSymbol => TermRef(prefix, sym)
        case _               => throw IllegalArgumentException(s"Invalid symbol $sym for NamedType")

    def apply(prefix: Type, name: Name)(using Context): NamedType =
      name match
        case name: TypeName => TypeRef(prefix, name)
        case name: TermName => TermRef(prefix, name)

    private[tastyquery] def apply(prefix: Type, external: Scala2ExternalSymRef)(using Context): NamedType =
      external.name match
        case _: TypeName => TypeRef(prefix, external)
        case _: TermName => TermRef(prefix, external)
  }

  /** The singleton type for path prefix#myDesignator. */
  final class TermRef private (
    val prefix: Type,
    private var myDesignator: TermSymbol | TermName | LookupIn | Scala2ExternalSymRef
  ) extends NamedType
      with SingletonType {

    type ThisName = TermName
    type ThisSymbolType = TermSymbol
    protected[this] type ThisDesignatorType = TermSymbol | TermName | LookupIn | Scala2ExternalSymRef

    protected[this] def designator: ThisDesignatorType = myDesignator

    protected[this] def storeComputedSymbol(sym: ThisSymbolType): Unit =
      myDesignator = sym

    override def toString(): String =
      s"TermRef($prefix, $myDesignator)"

    protected[this] def asThisSymbolType(sym: Symbol): ThisSymbolType =
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

    final def isOverloaded(using Context): Boolean =
      myDesignator match
        case LookupIn(pre, ref) =>
          pre.symbol.memberIsOverloaded(ref)
        case _ => false

    private[tastyquery] override def findMember(name: Name, pre: Type)(using Context): Symbol =
      underlying match
        case mt: MethodType if mt.paramInfos.isEmpty /*&& symbol.is(StableRealizable)*/ =>
          mt.resultType.findMember(name, pre)
        case tp =>
          tp.findMember(name, pre)

    protected[this] def withPrefix(prefix: Type, cachedSymbol: ThisSymbolType | Null)(using Context): Type =
      new TermRef(prefix, if cachedSymbol != null then cachedSymbol else designator)
  }

  object TermRef:
    def apply(prefix: Type, name: TermName): TermRef = new TermRef(prefix, name)
    def apply(prefix: Type, symbol: TermSymbol): TermRef = new TermRef(prefix, symbol)
    private[tastyquery] def apply(prefix: Type, designator: LookupIn): TermRef = new TermRef(prefix, designator)
    private[tastyquery] def apply(prefix: Type, external: Scala2ExternalSymRef): TermRef = new TermRef(prefix, external)
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

    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Symbol =
      symbol.getDecl(name).getOrElse {
        throw MemberNotFoundException(symbol, name)
      }

    override def toString(): String = s"PackageRef($fullyQualifiedName)"
  }

  final class TypeRef private (val prefix: Type, private var myDesignator: TypeName | TypeSymbol | Scala2ExternalSymRef)
      extends NamedType {

    type ThisName = TypeName
    type ThisSymbolType = TypeSymbol
    type ThisDesignatorType = TypeName | TypeSymbol | Scala2ExternalSymRef

    protected[this] def designator: ThisDesignatorType = myDesignator

    protected[this] def storeComputedSymbol(sym: ThisSymbolType): Unit =
      myDesignator = sym

    override def toString(): String =
      s"TypeRef($prefix, $myDesignator)"

    protected[this] def asThisSymbolType(sym: Symbol): ThisSymbolType =
      sym.asInstanceOf[TypeSymbol]

    private[tastyquery] def isLocalRef(sym: Symbol): Boolean =
      myDesignator == sym

    override def underlying(using Context): Type = symbol match
      case cls: ClassSymbol          => cls.classInfo
      case sym: TypeSymbolWithBounds => sym.upperBound

    private[tastyquery] override def findMember(name: Name, pre: Type)(using Context): Symbol =
      symbol match
        case sym: ClassSymbol =>
          ClassInfo.findMember(sym, name, pre)
        case sym: TypeSymbolWithBounds =>
          sym.upperBound.findMember(name, pre)

    protected[this] def withPrefix(prefix: Type, cachedSymbol: ThisSymbolType | Null)(using Context): Type =
      new TypeRef(prefix, if cachedSymbol != null then cachedSymbol else designator)
  }

  object TypeRef:
    def apply(prefix: Type, name: TypeName): TypeRef = new TypeRef(prefix, name)
    def apply(prefix: Type, symbol: TypeSymbol): TypeRef = new TypeRef(prefix, symbol)
    private[tastyquery] def apply(prefix: Type, external: Scala2ExternalSymRef): TypeRef = new TypeRef(prefix, external)
  end TypeRef

  object NoPrefix extends Type {
    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Symbol =
      throw new AssertionError(s"Cannot find member in NoPrefix")

    override def toString(): String = "NoPrefix"
  }

  final class ThisType(val tref: TypeRef) extends PathType with SingletonType {
    override def underlying(using Context): Type =
      tref // TODO This is probably wrong

    final def cls(using Context): ClassSymbol = tref.symbol.asClass

    override def toString(): String = s"ThisType($tref)"
  }

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

    private[tastyquery] override def findMember(name: Name, pre: Type)(using Context): Symbol =
      tycon match
        case tycon: TypeRef =>
          if tycon.symbol.isClass then tycon.findMember(name, pre)
          else ???
        case _ =>
          ???

    private[tastyquery] final def derivedAppliedType(tycon: Type, args: List[Type])(using Context): AppliedType =
      if ((tycon eq this.tycon) && (args eq this.args)) this
      else AppliedType(tycon, args)

    private[tastyquery] final def map(op: Type => Type)(using Context): AppliedType =
      derivedAppliedType(op(tycon), args.mapConserve(op))

    override def toString(): String = s"AppliedType($tycon, $args)"
  }

  /** A by-name parameter type of the form `=> T`, or the type of a method with no parameter list. */
  final class ExprType(val resultType: Type) extends TypeProxy with MethodicType {
    override def underlying(using Context): Type = resultType

    private[tastyquery] final def derivedExprType(resultType: Type)(using Context): ExprType =
      if (resultType eq this.resultType) this else ExprType(resultType)

    override def toString(): String = s"ExprType($resultType)"
  }

  sealed trait LambdaType extends Binders with TermType {
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
    private[tastyquery] def integrate(params: List[Symbol], tp: Type)(using Context): Type =
      Substituters.subst(tp, params, paramRefs)

    private[tastyquery] final def derivedLambdaType(
      paramNames: List[ThisName] = this.paramNames,
      paramInfos: List[PInfo] = this.paramInfos,
      resType: Type = this.resultType
    )(using Context): This =
      if (paramNames eq this.paramNames) && (paramInfos eq this.paramInfos) && (resType eq this.resultType) then
        this.asInstanceOf[This]
      else newLikeThis(paramNames, paramInfos, resType)

    private def newLikeThis(paramNames: List[ThisName], paramInfos: List[PInfo], resType: Type)(using Context): This =
      companion(paramNames)(
        x => paramInfos.mapConserve(Substituters.subst(_, this, x).asInstanceOf[PInfo]),
        x => resType.subst(this, x)
      )
  }

  sealed abstract class LambdaTypeCompanion[N <: Name, PInfo <: Type | TypeBounds, LT <: LambdaType] {
    def apply(paramNames: List[N])(paramInfosExp: LT => List[PInfo], resultTypeExp: LT => Type)(using Context): LT

    def apply(paramNames: List[N], paramInfos: List[PInfo], resultType: Type)(using Context): LT =
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
        )(using ctx)
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
    private[tastyquery] def integrate(tparams: List[TypeParamSymbol], bounds: TypeBounds)(using Context): TypeBounds =
      Substituters.subst(bounds, tparams, paramRefs)
  end TypeLambdaType

  final class MethodType(val paramNames: List[TermName])(
    paramTypesExp: MethodType => List[Type],
    resultTypeExp: MethodType => Type
  ) extends MethodicType
      with TermLambdaType:
    type This = MethodType

    private var evaluating: Boolean = false
    private var myParamTypes: List[Type] | Null = null
    private var myRes: Type | Null = null

    private def initialize(): Unit =
      if evaluating then throw CyclicReferenceException(s"method [$paramNames]=>???")
      else
        evaluating = true
        myParamTypes = paramTypesExp(this)
        myRes = resultTypeExp(this)
        evaluating = false

    def paramTypes: List[Type] =
      if myParamTypes == null then initialize()
      myParamTypes.nn

    def resultType: Type =
      if myRes == null then initialize()
      myRes.nn

    def paramInfos: List[PInfo] =
      paramTypes

    def companion: LambdaTypeCompanion[TermName, Type, MethodType] = MethodType

    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Symbol =
      throw new AssertionError(s"Cannot find member in $this")

    override def toString: String =
      if evaluating then s"MethodType($paramNames)(<evaluating>...)"
      else s"MethodType($paramNames)($paramTypes, $resultType)"
  end MethodType

  object MethodType extends LambdaTypeCompanion[TermName, Type, MethodType]:
    def apply(paramNames: List[TermName])(paramInfosExp: MethodType => List[Type], resultTypeExp: MethodType => Type)(
      using Context
    ): MethodType =
      new MethodType(paramNames)(paramInfosExp, resultTypeExp)

    /** Produce method type from parameter symbols, with special mappings for repeated
      *  and inline parameters:
      *   - replace @repeated annotations on Seq or Array types by <repeated> types
      *   - add @inlineParam to inline parameters
      */
    private[tastyquery] def fromSymbols(params: List[TermSymbol], resultType: Type)(using Context): MethodType = {
      // def translateInline(tp: Type): Type = tp match {
      //   case ExprType(resType) => ExprType(AnnotatedType(resType, Annotation(defn.InlineParamAnnot)))
      //   case _ => AnnotatedType(tp, Annotation(defn.InlineParamAnnot))
      // }
      // def translateErased(tp: Type): Type = tp match {
      //   case ExprType(resType) => ExprType(AnnotatedType(resType, Annotation(defn.ErasedParamAnnot)))
      //   case _ => AnnotatedType(tp, Annotation(defn.ErasedParamAnnot))
      // }
      def paramInfo(param: TermSymbol) = {
        var paramType = param.declaredType //.annotatedToRepeated
        // if (param.is(Inline)) paramType = translateInline(paramType)
        // if (param.is(Erased)) paramType = translateErased(paramType)
        paramType
      }

      MethodType.apply(params.map(_.name.toTermName))(
        tl => params.map(p => tl.integrate(params, paramInfo(p))),
        tl => tl.integrate(params, resultType)
      )(using ctx)
    }

  final class PolyType private (val paramNames: List[TypeName])(
    boundsRest: PolyType => List[TypeBounds],
    resultRest: PolyType => Type
  ) extends MethodicType
      with Binders
      with TypeLambdaType {
    type This = PolyType

    private var evaluating: Boolean = false
    private var myBounds: List[TypeBounds] | Null = null
    private var myRes: Type | Null = null

    private def initialize(): Unit =
      if evaluating then throw CyclicReferenceException(s"polymorphic method [$paramNames]=>???")
      else
        evaluating = true
        myBounds = boundsRest(this)
        myRes = resultRest(this)
        evaluating = false

    def paramTypeBounds: List[TypeBounds] =
      if myBounds == null then initialize()
      myBounds.nn

    def resultType: Type =
      if myRes == null then initialize()
      myRes.nn

    def paramInfos: List[PInfo] = paramTypeBounds

    def companion: LambdaTypeCompanion[TypeName, TypeBounds, PolyType] =
      PolyType

    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Symbol =
      throw new AssertionError(s"Cannot find member in $this")

    override def toString: String =
      if evaluating then s"PolyType($paramNames)(<evaluating>...)"
      else s"PolyType($paramNames)($myBounds, $myRes)"
  }

  object PolyType extends TypeLambdaTypeCompanion[PolyType]:

    def apply(
      paramNames: List[TypeName]
    )(paramTypeBoundsExp: PolyType => List[TypeBounds], resultTypeExp: PolyType => Type)(using Context): PolyType =
      new PolyType(paramNames)(paramTypeBoundsExp, resultTypeExp)

    def rec(
      paramNames: List[TypeName]
    )(boundsRest: Binders => List[TypeBounds], resultRest: Binders => Type): PolyType =
      val tpe = new PolyType(paramNames)(boundsRest, resultRest)
      tpe.resultType // initialize now
      tpe

    private[tastyquery] def fromParams(params: List[TypeParam], resultType: Type)(using Context): Type =
      if params.isEmpty then resultType
      else
        val paramNames = params.map(_.name)
        val paramTypeBounds = params.map(_.computeDeclarationTypeBounds())
        val paramSyms = params.map(_.symbol)
        apply(paramNames)(
          polyType => paramTypeBounds.map(polyType.integrate(paramSyms, _)),
          polyType => polyType.integrate(paramSyms, resultType)
        )
  end PolyType

  /** Encapsulates the binders associated with a ParamRef. */
  sealed trait Binders

  sealed trait TypeBinders extends Binders:
    def paramRefs: List[TypeParamRef]
    def lookupRef(name: TypeName): Option[Type]

  sealed trait BoundType extends Type:
    type BindersType <: Binders
    def binders: BindersType
    private[tastyquery] def copyBoundType(newBinders: BindersType): Type

  sealed trait ParamRef extends BoundType:
    def paramNum: Int

  final class TypeLambda(val paramNames: List[TypeName])(
    paramTypeBoundsExp: TypeLambda => List[TypeBounds],
    resultTypeExp: TypeLambda => Type
  ) extends TypeProxy
      with TermType
      with TypeLambdaType {
    type This = TypeLambda

    private var evaluating: Boolean = false
    private var myBounds: List[TypeBounds] | Null = null
    private var myRes: Type | Null = null

    private def initialize(): Unit =
      if evaluating then throw CyclicReferenceException(s"type lambda [$paramNames]=>???")
      else
        evaluating = true
        myBounds = paramTypeBoundsExp(this)
        myRes = resultTypeExp(this)
        evaluating = false

    def paramTypeBounds: List[TypeBounds] =
      if myBounds == null then initialize()
      myBounds.nn

    def resultType: Type =
      if myRes == null then initialize()
      myRes.nn

    def paramInfos: List[PInfo] = paramTypeBounds

    def companion: LambdaTypeCompanion[TypeName, TypeBounds, TypeLambda] = TypeLambda

    override def underlying(using Context): Type = defn.AnyType

    override def toString: String =
      if evaluating then s"TypeLambda($paramNames)(<evaluating>)"
      else s"TypeLambda($paramNames)($myRes)"
  }

  object TypeLambda extends TypeLambdaTypeCompanion[TypeLambda]:
    def apply(
      paramNames: List[TypeName]
    )(paramInfosExp: TypeLambda => List[TypeBounds], resultTypeExp: TypeLambda => Type)(using Context): TypeLambda =
      new TypeLambda(paramNames)(paramInfosExp, resultTypeExp)

    def rec(
      paramNames: List[TypeName]
    )(paramTypeBoundsExp: Binders => List[TypeBounds], resultTypeExp: Binders => Type): TypeLambda =
      val tpe = new TypeLambda(paramNames)(paramTypeBoundsExp, resultTypeExp)
      tpe.resultType // initialize now
      tpe

    private[tastyquery] def fromParams(params: List[TypeParam])(resultTypeExp: TypeLambda => Type)(
      using Context
    ): TypeLambda =
      apply(params.map(_.name))(_ => params.map(_.computeDeclarationTypeBounds()), resultTypeExp)(using ctx)
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
  final class AnnotatedType(val typ: Type, val annotation: Tree) extends TypeProxy with ValueType {
    override def underlying(using Context): Type = typ

    private[tastyquery] final def derivedAnnotatedType(typ: Type, annotation: Tree)(using Context): AnnotatedType =
      if ((typ eq this.typ) && (annotation eq this.annotation)) this
      else AnnotatedType(typ, annotation)

    override def toString(): String = s"AnnotatedType($typ, $annotation)"
  }

  sealed abstract class RefinedOrRecType extends TypeProxy

  /** A refined type `parent { type refinedName <:> refinedInfo }`
    * @param parent      The type being refined
    * @param refinedName The name of the refinement declaration
    * @param refinedInfo The info of the refinement declaration
    */
  final class RefinedType(val parent: Type, val refinedName: Name, val refinedInfo: TypeBounds)
      extends RefinedOrRecType
      with ValueType {
    override def underlying(using Context): Type = parent

    private[tastyquery] final def derivedRefinedType(parent: Type, refinedName: Name, refinedInfo: TypeBounds)(
      using Context
    ): Type =
      if ((parent eq this.parent) && (refinedName eq this.refinedName) && (refinedInfo eq this.refinedInfo)) this
      else RefinedType(parent, refinedName, refinedInfo)

    override def toString(): String = s"RefinedType($parent, $refinedName, $refinedInfo)"
  }

  final class RecType private (parentExp: RecType => Type) extends RefinedOrRecType with Binders:
    val parent: Type = parentExp(this: @unchecked)

    def underlying(using Context): Type = parent
  end RecType

  object RecType:
    def apply(parentExp: RecType => Type): RecType =
      new RecType(parentExp) // TODO? Perform normalization like dotc?
  end RecType

  sealed abstract class TypeBounds(val low: Type, val high: Type) extends TypeMappable {
    type ThisTypeMappableType = TypeBounds

    /** The non-alias type bounds type with given bounds */
    private[tastyquery] def derivedTypeBounds(low: Type, high: Type)(using Context): TypeBounds =
      if ((low eq this.low) && (high eq this.high)) this
      else RealTypeBounds(low, high)
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

  final class BoundedType(val bounds: TypeBounds, val alias: Type) extends Type {
    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Symbol =
      bounds.high.findMember(name, pre)

    override def toString(): String = s"BoundedType($bounds, $alias)"
  }

  final class NamedTypeBounds(val name: TypeName, val bounds: TypeBounds) extends Type {
    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Symbol =
      bounds.high.findMember(name, pre)

    override def toString(): String = s"NamedTypeBounds($name, $bounds)"
  }

  final class WildcardTypeBounds(val bounds: TypeBounds) extends TypeProxy {
    override def underlying(using Context): Type = bounds.high

    private[tastyquery] def derivedWildcardTypeBounds(bounds: TypeBounds)(using Context): WildcardTypeBounds =
      if bounds eq this.bounds then this
      else WildcardTypeBounds(bounds)

    override def toString(): String = s"WildcardTypeBounds($bounds)"
  }

  // ----- Ground Types -------------------------------------------------

  final class OrType(val first: Type, val second: Type) extends GroundType with ValueType {
    private var myJoin: Type | Null = _

    /** Returns the closest non-OrType type above this one. */
    def join(using Context): Type = {
      val myJoin = this.myJoin
      if (myJoin != null) then myJoin
      else
        val computedJoin = defn.ObjectType // TypeOps.orDominator(this)
        this.myJoin = computedJoin
        computedJoin
    }

    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Symbol =
      join.findMember(name, pre)

    private[tastyquery] def derivedOrType(first: Type, second: Type)(using Context): Type =
      if (first eq this.first) && (second eq this.second) then this
      else OrType.make(first, second)

    override def toString(): String = s"OrType($first, $second)"
  }

  object OrType {
    private[tastyquery] def make(first: Type, second: Type)(using Context): Type =
      if (first eq second) first
      else OrType(first, second)
  }

  final class AndType(val first: Type, val second: Type) extends GroundType with ValueType {
    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Symbol =
      first.findMember(name, pre) // TODO 'meet' with second.findMember(name, pre)

    private[tastyquery] def derivedAndType(first: Type, second: Type)(using Context): Type =
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
    private[tastyquery] def make(first: Type, second: Type)(using Context): Type =
      // TODO Avoid &'ing with Any
      if first eq second then first
      else AndType(first, second)
  }

  final class ClassInfo(val cls: ClassSymbol) extends GroundType {
    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Symbol =
      ClassInfo.findMember(cls, name, pre)

    private[tastyquery] def derivedClassInfo(pre: Type)(using Context): ClassInfo =
      this // so far do not store pre in ClassInfo

    override def toString(): String = s"ClassInfo($cls)"
  }

  object ClassInfo:
    private[Types] def findMember(cls: ClassSymbol, name: Name, pre: Type)(using Context): Symbol =
      cls.findMember(pre, name).getOrElse {
        throw new AssertionError(s"Cannot find member named '$name' in $pre")
      }
  end ClassInfo

  object NoType extends GroundType {
    private[tastyquery] def findMember(name: Name, pre: Type)(using Context): Symbol =
      throw new AssertionError(s"Cannot find member in NoType")

    override def toString(): String = "NoType"
  }
}
