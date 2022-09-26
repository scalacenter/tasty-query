package tastyquery.ast

import scala.annotation.{constructorOnly, tailrec}
import scala.collection.mutable

import dotty.tools.tasty.TastyFormat.NameTags
import tastyquery.Contexts.*
import tastyquery.ast.Constants.Constant
import tastyquery.ast.Flags.*
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Trees.{EmptyTree, Tree, TypeParam}
import tastyquery.ast.Names.*

import tastyquery.util.syntax.chaining.given

object Types {
  type Designator = Symbol | Name | LookupIn | Scala2ExternalSymRef

  case class LookupIn(pre: TypeRef, sel: SignedName)

  case class Scala2ExternalSymRef(owner: Symbol, path: List[Name]) {
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
        case tpe @ AppliedType(tycon, targs) =>
          if tycon.isRef(defn.ArrayClass) then
            val List(targ) = targs: @unchecked
            arrayOf(targ).arrayOf()
          else arrayOf(tycon)
        case tpe: Symbolic =>
          val sym = tpe.symbol
          if sym.isClass then ClassRef(sym.asClass).arrayOf()
          else arrayOf(sym.declaredType)
        case tpe: TypeParamRef           => arrayOfBounds(tpe.bounds)
        case WildcardTypeBounds(bounds)  => arrayOfBounds(bounds)
        case BoundedType(bounds, NoType) => arrayOfBounds(bounds)
        case BoundedType(_, alias)       => arrayOf(alias)
        case _ =>
          preErase(tpe).arrayOf()
      end arrayOf

      tpe.widen match
        case tpe @ AppliedType(tycon, targs) =>
          if tycon.isRef(defn.ArrayClass) then
            val List(targ) = targs: @unchecked
            arrayOf(targ)
          else
            tycon match
              case tycon: Symbolic if tycon.symbol.isClass =>
                // Fast path
                ClassRef(tycon.symbol.asClass)
              case _ =>
                preErase(tpe.translucentSuperType)
        case tpe: Symbolic =>
          tpe.resolveToSymbol match
            case cls: ClassSymbol =>
              ClassRef(cls)
            case sym =>
              if sym.isAllOf(ClassTypeParam) then preErase(sym.declaredType.upperBound)
              else preErase(sym.declaredType)
        case tpe: TypeParamRef =>
          preErase(tpe.bounds.high)
        case AndType(left, right) =>
          // TODO Take `right` into account. Currently we just try not to crash.
          preErase(left)
        case OrType(left, right) =>
          // TODO Take `right` into account. Currently we just try not to crash.
          preErase(left)
        case WildcardTypeBounds(bounds) =>
          preErase(bounds.high)
        case BoundedType(bounds, NoType) =>
          preErase(bounds.high)
        case BoundedType(_, alias) =>
          preErase(alias)
        case tpe =>
          throw IllegalStateException(s"Cannot erase $tpe")
    end preErase

    private def finishErase(typeRef: ErasedTypeRef)(using Context): ErasedTypeRef =
      def valueClass(cls: ClassSymbol): ErasedTypeRef =
        val ctor = cls.getDecl(nme.Constructor).get
        val List(List(param)) = ctor.paramSymss.dropWhile(_.headOption.exists(_.isType)): @unchecked
        val paramType = param.declaredType
        erase(paramType)

      typeRef match
        case ClassRef(cls) =>
          if cls == defn.AnyClass || cls == defn.AnyValClass then ClassRef(defn.ObjectClass)
          else if cls == defn.RepeatedParamClass then ClassRef(defn.SeqClass)
          else if cls == defn.ByNameParamClass2x then ClassRef(defn.Function0Class)
          else if cls.isDerivedValueClass then valueClass(cls)
          else typeRef
        case ArrayTypeRef(_, _) =>
          typeRef
    end finishErase
  }

  sealed trait TypeMappable:
    type ThisTypeMappableType >: this.type <: TypeMappable
  end TypeMappable

  abstract class Type extends TypeMappable {
    type ThisTypeMappableType = Type

    /** The class symbol of this type, None if reduction is not possible */
    private[tastyquery] final def classSymbol(using Context): Option[ClassSymbol] = this.widen match
      case tpe: Symbolic =>
        val sym = tpe.resolveToSymbol
        if sym.isClass then Some(sym.asClass)
        else sym.declaredType.classSymbol
      case info: ClassInfo =>
        Some(info.cls)
      case _ => None

    /** The type parameters of this type are:
      * For a ClassInfo type, the type parameters of its class.
      * For a typeref referring to a class, the type parameters of the class.
      * For a refinement type, the type parameters of its parent, dropping
      * any type parameter that is-rebound by the refinement.
      *
      * For any *-kinded type, returns `Nil`.
      */
    private[Types] final def typeParams(using Context): List[ParamInfo.TypeParamInfo] =
      this match
        case self: TypeRef =>
          val tsym = self.symbol
          if (tsym.isClass) tsym.typeParams
          else tsym.declaredType.typeParams
        case self: AppliedType =>
          if (self.tycon.typeSymbol.isClass) Nil
          else self.superType.typeParams
        case self: ClassInfo =>
          self.cls.typeParams
        case _: SingletonType | _: RefinedType =>
          Nil
        case WildcardTypeBounds(bounds) =>
          bounds.high.typeParams
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
          case dealiased @ WildcardTypeBounds(bounds) =>
            val newBounds = bounds match
              case bounds @ TypeAlias(alias) =>
                bounds.derivedTypeAlias(alias.appliedTo(args))
              case _ =>
                bounds.derivedTypeBounds(bounds.low.appliedTo(args), bounds.high.appliedTo(args))
            dealiased.derivedWildcardTypeBounds(newBounds)
          case dealiased =>
            AppliedType(this, args)
        }
    }

    final def applyIfParameterized(args: List[Type])(using Context): Type =
      if (args.nonEmpty /*typeParams.nonEmpty*/ ) appliedTo(args) else this

    /** Substitute all types of the form `TypeParamRef(from, N)` by `TypeParamRef(to, N)`. */
    final def subst(from: Binders, to: Binders)(using Context): Type =
      Substituters.subst(this, from, to)

    /** Substitute bound types by some other types */
    final def substParams(from: Binders, to: List[Type])(using Context): Type =
      Substituters.substParams(this, from, to)

    final def typeSymbol(using Context): Symbol = this match
      case tpe: TypeRef => tpe.resolveToSymbol
      case _            => NoSymbol

    final def termSymbol(using Context): Symbol = this match
      case tpe: TermRef => tpe.resolveToSymbol
      case _            => NoSymbol

    final def widenOverloads(using Context): Type =
      this.widen match
        case tp: TermRef => tp.underlying.widenOverloads
        case tp          => tp

    /** remove singleton types, ExprTypes and AnnotatedTypes */
    final def widen(using Context): Type = this match
      case _: TypeRef | _: MethodType | _: PolyType => this // fast path for most frequent cases
      case tp: TermRef => // fast path for next most frequent case
        if tp.isOverloaded then tp else tp.underlying.widen
      case tp: SingletonType => tp.underlying.widen
      case tp: ExprType      => tp.resType.widen
      case tp: AnnotatedType => tp.typ.widen
      case tp: RefinedType   => tp.parent.widen
      case tp                => tp

    final def widenIfUnstable(using Context): Type = this match
      // TODO Handle unstable term refs like method calls or values
      case tp: TermRef => tp
      case tp          => tp.widen

    def dealias(using Context): Type = dealias1(keepOpaques = false)

    private def dealias1(keepOpaques: Boolean)(using Context): Type = this match {
      case tp: TypeRef =>
        val tpSym = tp.symbol
        if tpSym.isClass then tp
        else
          tpSym.declaredType match
            case BoundedType(_, alias) if !keepOpaques && alias != NoType =>
              alias.dealias1(keepOpaques)
            case WildcardTypeBounds(TypeAlias(alias)) =>
              alias.dealias1(keepOpaques)
            case _ =>
              tp
      case app @ AppliedType(tycon, _) =>
        val tycon1 = tycon.dealias1(keepOpaques)
        if (tycon1 ne tycon) app.superType.dealias1(keepOpaques)
        else this
      case tp: AnnotatedType =>
        tp.typ.dealias1(keepOpaques)
      case _ =>
        this
    }

    /** The normalized prefix of this type is:
      *  For an alias type, the normalized prefix of its alias
      *  For all other named type and class infos: the prefix.
      *  Inherited by all other type proxies.
      *  `NoType` for all other types.
      */
    @tailrec final def normalizedPrefix(using Context): Type = this match {
      case tp: NamedType =>
        if (tp.symbol.declaredType.isTypeAlias) tp.symbol.declaredType.normalizedPrefix else tp.prefix
      case tp: ClassInfo =>
        // TODO tp.prefix
        tp.cls.accessibleThisType
      case tp: TypeProxy =>
        tp.superType.normalizedPrefix
      case _ =>
        NoType
    }

    final def isTypeAlias: Boolean = this match
      case WildcardTypeBounds(bounds) => bounds.isInstanceOf[TypeAlias]
      case _                          => false

    /** The basetype of this type with given class symbol, NoType if `base` is not a class. */
    final def baseType(base: Symbol)(using Context): Type =
      base match
        case base: ClassSymbol => base.baseTypeOf(this)
        case _                 => NoType

    /** The member with given `name` and required and/or excluded flags */
    final def member(name: Name)(using Context): Symbol =
      // We need a valid prefix for `asSeenFrom`
      val pre = this match
        case tp: ClassInfo => ??? // tp.appliedRef
        case _             => widenIfUnstable
      findMember(name, pre)

    /** Find member of this type with given `name`, all `required`
      * flags and no `excluded` flag and produce a denotation that contains
      * the type of the member as seen from given prefix `pre`.
      */
    def findMember(name: Name, pre: Type)(using Context): Symbol

    private[Types] def lookupRefined(name: Name)(using Context): Type =
      NoType

    /** True iff `sym` is a symbol of a class type parameter and the reference
      * `<pre> . <sym>` is an actual argument reference, i.e., `pre` is not the
      * ThisType of `sym`'s owner, or a reference to `sym`'s owner.'
      */
    def isArgPrefixOf(sym: Symbol)(using Context): Boolean =
      sym.exists
        && !sym.owner.isPackage // Early exit if possible because the next check would force SymbolLoaders
        && sym.isAllOf(ClassTypeParam)
        && {
          this match
            case tp: ThisType => tp.cls ne sym.owner
            case tp: TypeRef  => tp.symbol ne sym.owner
            case _            => true
        }

    def asSeenFrom(pre: Type, cls: Symbol)(using Context): Type =
      TypeOps.asSeenFrom(this, pre, cls)

    final def isRef(sym: Symbol)(using Context): Boolean =
      this match {
        case tpe: NamedType   => tpe.resolveToSymbol == sym
        case tpe: AppliedType => tpe.underlying.isRef(sym)
        case tpe: ExprType    => tpe.underlying.isRef(sym)
        case _                => false // todo: add ProxyType (need to fill in implementations of underlying)
      }

    /** Is this type exactly Nothing (no vars, aliases, refinements etc allowed)? */
    def isExactlyNothing(using Context): Boolean = this match
      case tp: TypeRef =>
        tp.name == tpnme.Nothing && (tp.symbol eq ctx.findSymbolFromRoot(nme.scalaPackageName :: tpnme.Nothing :: Nil))
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
    def lowerBound: Type = this match {
      case WildcardTypeBounds(bounds) => bounds.low
      case _                          => this
    }

    /** The upper bound of a TypeBounds type, the type itself otherwise */
    def upperBound: Type = this match {
      case WildcardTypeBounds(bounds) => bounds.high
      case _                          => this
    }

    /** Is self type bounded by a type lambda or AnyKind? */
    def isLambdaSub(using Context): Boolean = false // TODO hkResult.exists

    def &(that: Type)(using Context): Type =
      // TypeComparer.glb(this, that)
      AndType.make(this, that)

    def |(that: Type)(using Context): Type =
      // TypeCompare.lub(this, that)
      OrType.make(this, that)

    final def select(sym: Symbol)(using Context): Type =
      NamedType(this, sym) // dotc also calls reduceProjection here, should we do it?
  }

  private def scalaPackage: PackageRef = PackageRef(FullyQualifiedName.scalaPackageName)

  private def javalangPackage: PackageRef = PackageRef(FullyQualifiedName.javaLangPackageName)

  private def scalaDot(name: TypeName): TypeRef =
    TypeRef(scalaPackage, name)

  private def javalangDot(name: TypeName): Type =
    TypeRef(javalangPackage, name)

  def AnyType: Type = scalaDot(tpnme.Any)
  def NothingType: Type = scalaDot(tpnme.Nothing)
  def NullType: Type = scalaDot(tpnme.Null)

  def ArrayTypeUnapplied: TypeRef = scalaDot(tpnme.Array)
  def ArrayTypeOf(tpe: Type): AppliedType = AppliedType(ArrayTypeUnapplied, List(tpe))

  def SeqTypeUnapplied: TypeRef = scalaDot(tpnme.Seq)
  def SeqTypeOf(tpe: Type): AppliedType = AppliedType(SeqTypeUnapplied, List(tpe))

  def UnitType: Type = scalaDot(tpnme.Unit)
  def BooleanType: Type = scalaDot(tpnme.Boolean)
  def CharType: Type = scalaDot(tpnme.Char)
  def ByteType: Type = scalaDot(tpnme.Byte)
  def ShortType: Type = scalaDot(tpnme.Short)
  def IntType: Type = scalaDot(tpnme.Int)
  def LongType: Type = scalaDot(tpnme.Long)
  def FloatType: Type = scalaDot(tpnme.Float)
  def DoubleType: Type = scalaDot(tpnme.Double)

  def StringType: Type = javalangDot(tpnme.String)
  def ObjectType: Type = javalangDot(tpnme.Object)
  def ClassTypeOf(cls: Type): Type = AppliedType(javalangDot(tpnme.Class), List(cls))

  def UnconstrainedTypeBounds: TypeBounds = RealTypeBounds(NothingType, AnyType)

  // ----- Type categories ----------------------------------------------

  // Every type is expected to inherit either TypeProxy or GroundType.

  /** Type proxies.
    * Each implementation is expected to redefine the `underlying` method.
    */
  abstract class TypeProxy extends Type {

    /** The type to which this proxy forwards operations. */
    def underlying(using Context): Type

    /** The closest supertype of this type.
      *
      * This is the same as `underlying`, except that
      *   - instead of a TypeBounds type it returns its upper bound, and
      *   - for applied types it returns the upper bound of the constructor re-applied to the arguments.
      */
    def superType(using Context): Type = underlying match {
      case WildcardTypeBounds(bounds) => bounds.high
      case st                         => st
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

    def findMember(name: Name, pre: Type)(using Context): Symbol =
      underlying.findMember(name, pre)
  }

  /** Non-proxy types */
  abstract class GroundType extends Type {}

  // ----- Marker traits ------------------------------------------------

  /** A marker trait for types that apply only to term symbols or that
    * represent higher-kinded types.
    */
  trait TermType extends Type

  trait MethodicType extends TermType

  /** A marker trait for types that can be types of values or prototypes of value types */
  trait ValueTypeOrProto extends TermType

  /** A marker trait for types that can be types of values or that are higher-kinded */
  trait ValueType extends ValueTypeOrProto

  /** A marker trait for types that are guaranteed to contain only a
    * single non-null value (they might contain null in addition).
    */
  trait SingletonType extends TypeProxy with ValueType {
    def isOverloaded(using Context): Boolean = false
  }

  trait PathType extends TypeProxy with ValueType {
    final def select(name: Name): NamedType =
      if name.isTermName then TermRef(this, name)
      else TypeRef(this, name)
  }

  trait Symbolic {
    final def symbol(using Context): Symbol =
      resolveToSymbol

    def resolveToSymbol(using Context): Symbol
  }

  // ----- Type Proxies -------------------------------------------------

  abstract class NamedType extends PathType with Symbolic {
    self =>

    type ThisType >: this.type <: NamedType
    type ThisName <: Name

    val prefix: Type

    def designator: Designator

    protected def designator_=(d: Designator): Unit

    private var myName: ThisName | Null = null

    def isType: Boolean = isInstanceOf[TypeRef]

    def isTerm: Boolean = isInstanceOf[TermRef]

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

    def selectIn(name: SignedName, in: TypeRef): TermRef =
      TermRef(this, LookupIn(in, name))

    // overridden in package references
    override def resolveToSymbol(using Context): Symbol = designator match {
      case sym: Symbol => sym
      case LookupIn(pre, name) =>
        val sym = TermRef(pre, name).resolveToSymbol
        designator = sym
        sym
      case Scala2ExternalSymRef(owner, path) =>
        val sym = path.foldLeft(owner) { (owner, name) =>
          val cls = if owner.isTerm then owner.declaredType.asInstanceOf[Symbolic].symbol else owner
          cls.asClass.getDecl(name).getOrElse {
            throw new SymbolLookupException(name, s"cannot find symbol $owner.$name")
          }
        }
        designator = sym
        sym
      case name: Name =>
        @tailrec
        def findPrefixSym(prefix: Type): Symbol = prefix match {
          case NoPrefix =>
            throw new SymbolLookupException(name, "reference by name to a local symbol")
          case ref: PackageRef =>
            ref.symbol
          case t: TermRef =>
            findPrefixSym(t.underlying)
          case other: Symbolic =>
            other.resolveToSymbol
          case AppliedType(tycon, _) =>
            findPrefixSym(tycon)
          case prefix =>
            throw new SymbolLookupException(name, s"unexpected prefix type $prefix")
        }
        val prefixSym = findPrefixSym(prefix)
        val sym = {
          prefixSym match
            case declaring: DeclaringSymbol =>
              val candidate = declaring.getDecl(name)
              candidate.getOrElse {
                val msg = this match
                  case TermRef(_, name: SignedName) if declaring.memberPossiblyOverloaded(name) =>
                    def debugSig(sym: Symbol): String = sym.signature match {
                      case Some(sig) => sig.toDebugString
                      case None      => "<Not A Method>"
                    }
                    val debugQueried = name.sig.toDebugString
                    val debugCandidates = declaring.memberOverloads(name).map(debugSig).mkString("\n - ", "\n - ", "")
                    s"""could not resolve overload for `${name.underlying}`:
                       |Queried signature:
                       | - $debugQueried
                       |Overloads found with signatures:$debugCandidates
                       |Perhaps the classpath is out of date.""".stripMargin
                  case _ =>
                    val possible = declaring.declarations.map(_.name.toDebugString).mkString("[", ", ", "]")
                    s"not a member of $prefixSym, found possible members: $possible."
                throw SymbolLookupException(name, msg)
              }
            case _ =>
              throw SymbolLookupException(name, s"$prefixSym is not a package or class")
        }
        designator = sym
        sym
    }

    /** The argument corresponding to class type parameter `tparam` as seen from
      * prefix `pre`. Can produce a TypeBounds type if `widenAbstract` is true,
      * or prefix is an & or | type and parameter is non-variant.
      * Otherwise, a typebounds argument is dropped and the original type parameter
      * reference is returned.
      */
    def argForParam(pre: Type, widenAbstract: Boolean = false)(using Context): Type = {
      val tparam = symbol
      val cls = tparam.owner
      val base = pre.baseType(cls)
      base match {
        case AppliedType(_, allArgs) =>
          var tparams = cls.typeParams
          var args = allArgs
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
    def derivedSelect(prefix: Type)(using Context): Type =
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
        withPrefix(prefix)
      }

    private def withPrefix(prefix: Type)(using Context): Type =
      NamedType(prefix, designator)
  }

  object NamedType {
    private def isType(designator: Designator): Boolean = designator match
      case designator: Symbol               => designator.isType
      case designator: Name                 => designator.isTypeName
      case designator: LookupIn             => false // always a SignedName, which is a TermName by construction
      case designator: Scala2ExternalSymRef => designator.name.isTypeName

    def apply(prefix: Type, designator: Designator)(using Context): NamedType =
      if (isType(designator)) TypeRef(prefix, designator)
      else TermRef(prefix, designator)

    def apply(prefix: Type, sym: Symbol)(using Context): NamedType =
      if (sym.isType) TypeRef(prefix, sym)
      else TermRef(prefix, sym)

    def apply(prefix: Type, name: Name)(using Context): NamedType =
      if (name.isTypeName) TypeRef(prefix, name)
      else TermRef(prefix, name)
  }

  /** A reference to an implicit definition. This can be either a TermRef or a
    * Implicits.RenamedImplicitRef.
    */
  trait ImplicitRef {
    def implicitName: TermName
    def underlyingRef: TermRef
  }

  abstract class SymResolutionProblem(msg: String, cause: Throwable | Null) extends Exception(msg, cause):
    def this(msg: String) = this(msg, null)

  class CyclicReference(val kind: String) extends Exception(s"cyclic evaluation of $kind")
  class NonMethodReference(val kind: String) extends Exception(s"reference to non method type in $kind")

  /** The singleton type for path prefix#myDesignator. */
  case class TermRef(override val prefix: Type, var myDesignator: Designator)
      extends NamedType
      with SingletonType
      with ImplicitRef {

    type ThisType = TermRef
    type ThisName = TermName

    override def designator: Designator = myDesignator

    override protected def designator_=(d: Designator): Unit = myDesignator = d

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
      val termSymbol = resolveToSymbol
      termSymbol.declaredType.asSeenFrom(prefix, termSymbol.owner)
    }

    override def isOverloaded(using Context): Boolean =
      myDesignator match
        case LookupIn(pre, ref) =>
          pre.resolveToSymbol.memberIsOverloaded(ref)
        case _ => false

    def implicitName: TermName = name

    def underlyingRef: TermRef = this

    override def findMember(name: Name, pre: Type)(using Context): Symbol =
      underlying match
        case mt: MethodType if mt.paramInfos.isEmpty /*&& resolveToSymbol.is(StableRealizable)*/ =>
          mt.resultType.findMember(name, pre)
        case tp =>
          tp.findMember(name, pre)
  }

  final case class PackageRef(fullyQualifiedName: FullyQualifiedName) extends Type {
    private var packageSymbol: PackageClassSymbol | Null = null

    def this(packageSym: PackageClassSymbol) =
      this(packageSym.fullName)
      packageSymbol = packageSym

    def symbol(using Context): PackageClassSymbol = {
      val local = packageSymbol
      if (local == null) {
        val resolved = ctx.findPackageFromRoot(fullyQualifiedName)
        packageSymbol = resolved
        resolved
      } else local
    }

    def findMember(name: Name, pre: Type)(using Context): Symbol =
      symbol.getDecl(name).getOrElse {
        throw SymbolLookupException(name, s"Cannot find a member $name in $symbol")
      }
  }

  object PackageRef {
    def apply(packageSym: PackageClassSymbol): PackageRef =
      new PackageRef(packageSym)
  }

  case class TypeRef(override val prefix: Type, private var myDesignator: Designator) extends NamedType {

    type ThisType = TypeRef
    type ThisName = TypeName

    override def designator: Designator = myDesignator

    override protected def designator_=(d: Designator): Unit = myDesignator = d

    private[tastyquery] def isLocalRef(sym: Symbol): Boolean =
      myDesignator == sym

    override def underlying(using Context): Type = symbol.declaredType

    override def findMember(name: Name, pre: Type)(using Context): Symbol =
      val sym = resolveToSymbol
      sym match
        case sym: ClassSymbol =>
          ClassInfo.findMember(sym, name, pre)
        case _ =>
          sym.declaredType.findMember(name, pre)
  }

  case object NoPrefix extends Type {
    def findMember(name: Name, pre: Type)(using Context): Symbol =
      throw new AssertionError(s"Cannot find member in NoPrefix")
  }

  case class ThisType(tref: TypeRef) extends PathType with SingletonType with Symbolic {
    override def underlying(using Context): Type =
      tref // TODO This is probably wrong

    override def resolveToSymbol(using Context): Symbol = tref.resolveToSymbol

    def cls(using Context): ClassSymbol = symbol.asClass
  }

  /** A constant type with single `value`. */
  case class ConstantType(value: Constant) extends TypeProxy with SingletonType {
    override def underlying(using Context): Type =
      value.wideType
  }

  /** A type application `C[T_1, ..., T_n]`
    * Typebounds for wildcard application: C[_], C[?]
    */
  case class AppliedType(tycon: Type, args: List[Type]) extends TypeProxy with ValueType {
    override def underlying(using Context): Type = tycon

    override def superType(using Context): Type =
      tycon match
        //case tycon: HKTypeLambda => defn.AnyType
        case tycon: TypeRef if tycon.symbol.isClass => tycon
        case tycon: TypeProxy                       => tycon.superType.applyIfParameterized(args)
        case _                                      => AnyType

    override def translucentSuperType(using Context): Type = tycon match
      case tycon: TypeRef if tycon.symbol.isOpaqueTypeAlias =>
        tycon.translucentSuperType.applyIfParameterized(args)
      case _ =>
        // tryNormalize.orElse(superType) // TODO for match types
        superType

    def tyconTypeParams(using Context): List[ParamInfo] =
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
    def isUnreducibleWild(using Context): Boolean =
      // TODO tycon.isLambdaSub && hasWildcardArg && !isMatchAlias
      false

    override def findMember(name: Name, pre: Type)(using Context): Symbol =
      tycon match
        case tycon: TypeRef =>
          if tycon.resolveToSymbol.isClass then tycon.findMember(name, pre)
          else ???
        case _ =>
          ???

    def derivedAppliedType(tycon: Type, args: List[Type])(using Context): AppliedType =
      if ((tycon eq this.tycon) && (args eq this.args)) this
      else AppliedType(tycon, args)

    def map(op: Type => Type)(using Context): AppliedType =
      derivedAppliedType(op(tycon), args.mapConserve(op))
  }

  /** A by-name parameter type of the form `=> T`, or the type of a method with no parameter list. */
  case class ExprType(resType: Type) extends TypeProxy with MethodicType {
    def resultType: Type = resType

    override def underlying(using Context): Type = resType

    def derivedExprType(resType: Type)(using Context): ExprType =
      if (resType eq this.resType) this else ExprType(resType)
  }

  trait LambdaType extends Binders with TermType {
    type ThisName <: Name
    type PInfo <: Type | TypeBounds
    type This <: LambdaType { type PInfo = LambdaType.this.PInfo }
    type ParamRefType <: ParamRef

    def paramNames: List[ThisName]
    def paramInfos: List[PInfo]
    def resType: Type

    protected def newParamRef(n: Int): ParamRefType

    def resultType: Type = resType

    val paramRefs: List[ParamRefType] =
      List.tabulate(paramNames.size)(newParamRef(_): @unchecked)

    def lookupRef(name: ThisName): Option[ParamRefType] =
      paramNames.indexOf(name) match
        case -1    => None
        case index => Some(paramRefs(index))

    def companion: LambdaTypeCompanion[ThisName, PInfo, This]

    final def derivedLambdaType(
      paramNames: List[ThisName] = this.paramNames,
      paramInfos: List[PInfo] = this.paramInfos,
      resType: Type = this.resType
    )(using Context): This =
      if (paramNames eq this.paramNames) && (paramInfos eq this.paramInfos) && (resType eq this.resType) then
        this.asInstanceOf[This]
      else newLikeThis(paramNames, paramInfos, resType)

    def newLikeThis(paramNames: List[ThisName], paramInfos: List[PInfo], resType: Type)(using Context): This =
      companion(paramNames)(
        x => paramInfos.mapConserve(Substituters.subst(_, this, x).asInstanceOf[PInfo]),
        x => resType.subst(this, x)
      )
  }

  abstract class LambdaTypeCompanion[N <: Name, PInfo <: Type | TypeBounds, LT <: LambdaType] {
    def apply(paramNames: List[N])(paramInfosExp: LT => List[PInfo], resultTypeExp: LT => Type)(using Context): LT

    def apply(paramNames: List[N], paramInfos: List[PInfo], resultType: Type)(using Context): LT =
      apply(paramNames)(_ => paramInfos, _ => resultType)
  }

  trait TermLambdaType extends LambdaType:
    type ThisName = TermName
    type PInfo = Type
    type This <: TermLambdaType
    type ParamRefType = TermParamRef

    protected def newParamRef(n: Int): ParamRefType = TermParamRef(this, n)
  end TermLambdaType

  trait TypeLambdaType extends LambdaType with TypeBinders:
    type ThisName = TypeName
    type PInfo = TypeBounds
    type This <: TypeLambdaType
    type ParamRefType = TypeParamRef

    protected def newParamRef(n: Int): ParamRefType = TypeParamRef(this, n)

    def instantiate(args: List[Type])(using Context): Type =
      Substituters.substParams(resType, this, args)

    /** The type `[tparams := paramRefs] tp`, where `tparams` can be
      * either a list of type parameter symbols or a list of lambda parameters
      */
    private[tastyquery] def integrate(params: List[Symbol], tp: Type)(using Context): Type =
      Substituters.subst(tp, params, paramRefs)

    /** The type `[tparams := paramRefs] tp`, where `tparams` can be
      * either a list of type parameter symbols or a list of lambda parameters
      */
    private[tastyquery] def integrate(params: List[Symbol], bounds: TypeBounds)(using Context): TypeBounds =
      Substituters.subst(bounds, params, paramRefs)
  end TypeLambdaType

  case class MethodType(paramNames: List[TermName])(
    paramTypesExp: MethodType => List[Type],
    resultTypeExp: MethodType => Type
  ) extends MethodicType
      with TermLambdaType:
    type This = MethodType

    private var evaluating: Boolean = true
    val paramTypes: List[Type] = paramTypesExp(this: @unchecked)
    val resType: Type = resultTypeExp(this: @unchecked)
    evaluating = false

    def paramInfos: List[PInfo] = paramTypes

    def companion: LambdaTypeCompanion[TermName, Type, MethodType] = MethodType

    def findMember(name: Name, pre: Type)(using Context): Symbol =
      throw new AssertionError(s"Cannot find member in $this")

    override def toString: String =
      if evaluating then s"MethodType($paramNames)(<evaluating>...)"
      else s"MethodType($paramNames)($paramTypes, $resType)"
  end MethodType

  object MethodType extends LambdaTypeCompanion[TermName, Type, MethodType]:
    def apply(paramNames: List[TermName])(paramInfosExp: MethodType => List[Type], resultTypeExp: MethodType => Type)(
      using Context
    ): MethodType =
      new MethodType(paramNames)(paramInfosExp, resultTypeExp)

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
      if evaluating then throw CyclicReference(s"polymorphic method [$paramNames]=>???")
      else
        evaluating = true
        myBounds = boundsRest(this)
        myRes = resultRest(this)
        evaluating = false

    def paramTypeBounds: List[TypeBounds] =
      if myBounds == null then initialize()
      myBounds.nn

    def resType: Type =
      if myRes == null then initialize()
      myRes.nn

    def paramInfos: List[PInfo] = paramTypeBounds

    def companion: LambdaTypeCompanion[TypeName, TypeBounds, PolyType] =
      PolyType

    def findMember(name: Name, pre: Type)(using Context): Symbol =
      throw new AssertionError(s"Cannot find member in $this")

    override def toString: String =
      if evaluating then s"PolyType($paramNames)(<evaluating>...)"
      else s"PolyType($paramNames)($myBounds, $myRes)"
  }

  object PolyType extends LambdaTypeCompanion[TypeName, TypeBounds, PolyType]:
    def apply(
      paramNames: List[TypeName]
    )(paramTypeBoundsExp: PolyType => List[TypeBounds], resultTypeExp: PolyType => Type)(using Context): PolyType =
      new PolyType(paramNames)(paramTypeBoundsExp, resultTypeExp)

    def rec(
      paramNames: List[TypeName]
    )(boundsRest: Binders => List[TypeBounds], resultRest: Binders => Type): PolyType =
      val tpe = new PolyType(paramNames)(boundsRest, resultRest)
      tpe.resType // initialize now
      tpe

    def unapply(tpe: PolyType): (List[TypeName], List[TypeBounds], Type) =
      (tpe.paramNames, tpe.paramTypeBounds, tpe.resultType)

    def fromParams(params: List[TypeParam], resultType: Type)(using Context): Type =
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
    def copyBoundType(newBinders: BindersType): Type

  sealed trait ParamRef extends BoundType:
    def paramNum: Int

  case class TypeLambda(paramNames: List[TypeName])(
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
      if evaluating then throw CyclicReference(s"polymorphic method [$paramNames]=>???")
      else
        evaluating = true
        myBounds = paramTypeBoundsExp(this)
        myRes = resultTypeExp(this)
        evaluating = false

    def paramTypeBounds: List[TypeBounds] =
      if myBounds == null then initialize()
      myBounds.nn

    def resType: Type =
      if myRes == null then initialize()
      myRes.nn

    def paramInfos: List[PInfo] = paramTypeBounds

    def companion: LambdaTypeCompanion[TypeName, TypeBounds, TypeLambda] = TypeLambda

    override def underlying(using Context): Type = AnyType

    override def toString: String =
      if evaluating then s"TypeLambda($paramNames)(<evaluating>)"
      else s"TypeLambda($paramNames)($myRes)"
  }

  object TypeLambda extends LambdaTypeCompanion[TypeName, TypeBounds, TypeLambda]:
    def apply(
      paramNames: List[TypeName]
    )(paramInfosExp: TypeLambda => List[TypeBounds], resultTypeExp: TypeLambda => Type)(using Context): TypeLambda =
      new TypeLambda(paramNames)(paramInfosExp, resultTypeExp)

    def rec(
      paramNames: List[TypeName]
    )(paramTypeBoundsExp: Binders => List[TypeBounds], resultTypeExp: Binders => Type): TypeLambda =
      val tpe = new TypeLambda(paramNames)(paramTypeBoundsExp, resultTypeExp)
      tpe.resType // initialize now
      tpe

    def fromParams(params: List[TypeParam])(resultTypeExp: TypeLambda => Type)(using Context): TypeLambda =
      apply(params.map(_.name))(_ => params.map(_.computeDeclarationTypeBounds()), resultTypeExp)(using ctx)
  end TypeLambda

  case class TypeParamRef(binders: TypeLambdaType, paramNum: Int) extends TypeProxy with ValueType with ParamRef {
    type BindersType = TypeLambdaType

    def copyBoundType(newBinders: BindersType): Type =
      newBinders.paramRefs(paramNum)

    override def underlying(using Context): Type = bounds.high

    def paramName: TypeName = binders.paramNames(paramNum)

    def bounds(using Context): TypeBounds = binders.paramInfos(paramNum)

    override def toString: String = paramName.toString
  }

  case class TermParamRef(binders: TermLambdaType, paramNum: Int) extends ParamRef with SingletonType {
    type BindersType = TermLambdaType

    def copyBoundType(newBinders: BindersType): Type =
      newBinders.paramRefs(paramNum)

    def underlying(using Context): Type = binders.paramInfos(paramNum)
  }

  /** typ @ annot */
  case class AnnotatedType(typ: Type, annotation: Tree) extends TypeProxy with ValueType {
    override def underlying(using Context): Type = typ

    def derivedAnnotatedType(typ: Type, annotation: Tree)(using Context): AnnotatedType =
      if ((typ eq this.typ) && (annotation eq this.annotation)) this
      else AnnotatedType(typ, annotation)
  }

  abstract class RefinedOrRecType extends TypeProxy

  /** A refined type `parent { type refinedName <:> refinedInfo }`
    * @param parent      The type being refined
    * @param refinedName The name of the refinement declaration
    * @param refinedInfo The info of the refinement declaration
    */
  case class RefinedType(parent: Type, refinedName: Name, refinedInfo: TypeBounds)
      extends RefinedOrRecType
      with ValueType {
    override def underlying(using Context): Type = parent

    def derivedRefinedType(parent: Type, refinedName: Name, refinedInfo: TypeBounds)(using Context): Type =
      if ((parent eq this.parent) && (refinedName eq this.refinedName) && (refinedInfo eq this.refinedInfo)) this
      else RefinedType(parent, refinedName, refinedInfo)
  }

  final class RecType(parentExp: RecType => Type) extends RefinedOrRecType with Binders:
    val parent: Type = parentExp(this: @unchecked)

    def underlying(using Context): Type = parent
  end RecType

  object RecType:
    def apply(parentExp: RecType => Type): RecType =
      new RecType(parentExp) // TODO? Perform normalization like dotc?

    def unapply(recType: RecType): Some[Type] = Some(recType.parent)
  end RecType

  abstract class TypeBounds(val low: Type, val high: Type) extends TypeMappable {
    type ThisTypeMappableType = TypeBounds

    /** The non-alias type bounds type with given bounds */
    def derivedTypeBounds(low: Type, high: Type)(using Context): TypeBounds =
      if ((low eq this.low) && (high eq this.high)) this
      else RealTypeBounds(low, high)
  }

  case class RealTypeBounds(override val low: Type, override val high: Type) extends TypeBounds(low, high)

  case class TypeAlias(alias: Type) extends TypeBounds(alias, alias) {
    def derivedTypeAlias(alias: Type): TypeAlias =
      if alias eq this.alias then this
      else TypeAlias(alias)
  }

  case class BoundedType(bounds: TypeBounds, alias: Type) extends Type {
    def findMember(name: Name, pre: Type)(using Context): Symbol =
      bounds.high.findMember(name, pre)
  }

  case class NamedTypeBounds(name: TypeName, bounds: TypeBounds) extends Type {
    def findMember(name: Name, pre: Type)(using Context): Symbol =
      bounds.high.findMember(name, pre)
  }

  case class WildcardTypeBounds(bounds: TypeBounds) extends TypeProxy {
    override def underlying(using Context): Type = bounds.high

    def derivedWildcardTypeBounds(bounds: TypeBounds)(using Context): WildcardTypeBounds =
      if bounds eq this.bounds then this
      else WildcardTypeBounds(bounds)
  }

  // ----- Ground Types -------------------------------------------------

  case class OrType(first: Type, second: Type) extends GroundType with ValueType {
    private var myJoin: Type | Null = _

    /** Returns the closest non-OrType type above this one. */
    def join(using Context): Type = {
      val myJoin = this.myJoin
      if (myJoin != null) then myJoin
      else
        val computedJoin = ObjectType // TypeOps.orDominator(this)
        this.myJoin = computedJoin
        computedJoin
    }

    def findMember(name: Name, pre: Type)(using Context): Symbol =
      join.findMember(name, pre)

    def derivedOrType(first: Type, second: Type)(using Context): Type =
      if (first eq this.first) && (second eq this.second) then this
      else OrType.make(first, second)
  }

  object OrType {
    def make(first: Type, second: Type)(using Context): Type =
      if (first eq second) first
      else OrType(first, second)
  }

  case class AndType(first: Type, second: Type) extends GroundType with ValueType {
    def findMember(name: Name, pre: Type)(using Context): Symbol =
      first.findMember(name, pre) // TODO 'meet' with second.findMember(name, pre)

    def derivedAndType(first: Type, second: Type)(using Context): Type =
      if ((first eq this.first) && (second eq this.second)) this
      else AndType.make(first, second)

    def parts: List[Type] =
      def rec(tpe: Type, acc: mutable.ListBuffer[Type]): acc.type = tpe match
        case AndType(tp1, tp2) => rec(tp2, rec(tp1, acc))
        case tpe: Type         => acc += tpe
      rec(this, mutable.ListBuffer.empty).toList
  }

  object AndType {
    def make(first: Type, second: Type)(using Context): Type =
      // TODO Avoid &'ing with Any
      if first eq second then first
      else AndType(first, second)
  }

  case class ClassInfo(cls: ClassSymbol)(private var mkRawParents: (() => List[Type]) | Null) extends GroundType {
    var _rawParents: List[Type] | Null = null

    def rawParents: List[Type] =
      val localParents = _rawParents
      if localParents != null then localParents
      else
        val localFactory = mkRawParents
        if localFactory == null then throw CyclicReference(s"class info for ${cls.toDebugString}")
        else
          mkRawParents = null // we are evaluating the parents, avoid cycles by set to null
          val computedParents = localFactory()
          _rawParents = computedParents
          computedParents

    def findMember(name: Name, pre: Type)(using Context): Symbol =
      ClassInfo.findMember(cls, name, pre)

    def derivedClassInfo(pre: Type)(using Context): ClassInfo =
      this // so far do not store pre in ClassInfo
  }

  object ClassInfo:
    private[Types] def findMember(cls: ClassSymbol, name: Name, pre: Type)(using Context): Symbol =
      cls.findMember(pre, name).getOrElse {
        throw new AssertionError(s"Cannot find member named '$name' in $pre")
      }

    def direct(cls: ClassSymbol, rawParents: List[Type])(using Context): ClassInfo =
      ClassInfo(cls)(() => rawParents)
    def defer(cls: ClassSymbol, rawParents: => List[Type])(using Context): ClassInfo =
      ClassInfo(cls)(() => rawParents)

  case object NoType extends GroundType {
    def findMember(name: Name, pre: Type)(using Context): Symbol =
      throw new AssertionError(s"Cannot find member in NoType")
  }
}
