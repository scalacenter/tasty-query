package tastyquery.ast

import dotty.tools.tasty.TastyFormat.NameTags
import tastyquery.Contexts.{BaseContext, baseCtx, defn}
import tastyquery.ast.Constants.Constant
import tastyquery.ast.Names.{Name, QualifiedName, SimpleName, TermName, TypeName}
import tastyquery.ast.Symbols.*
import tastyquery.ast.Trees.{EmptyTree, Tree, TypeParam}
import tastyquery.ast.Names.*
import annotation.constructorOnly

import tastyquery.util.syntax.chaining.given

object Types {
  type Designator = Symbol | Name | LookupIn | Scala2ExternalSymRef

  case class LookupIn(pre: TypeRef, sel: SignedName)

  case class Scala2ExternalSymRef(owner: Symbol, path: List[Name]) {
    val name = path.last
  }

  object ErasedTypeRef {
    // TODO: improve this to match dotty:
    // - types must be erased before converting to TypeName
    // - use correct type erasure algorithm from Scala 3, with specialisations
    //   for Java types and Scala 2 types (i.e. varargs, value-classes)
    def erase(tpe: Type)(using BaseContext): TypeName =

      val scalaArray = ArrayTypeUnapplied.resolveToSymbol

      def specialise(arrayDims: Int, full: TermName): TermName =
        if arrayDims == 0 then full
        else
          val suffix = "[]" * arrayDims
          (full: @unchecked) match
            case QualifiedName(NameTags.QUALIFIED, pre, name) =>
              pre.select(name.append(suffix))
            case name: SimpleName =>
              name.append(suffix)

      def rec(arrayDims: Int, tpe: Type): TermName = tpe.widen match
        case AppliedType(tycon, List(targ)) if tycon.isRef(scalaArray) =>
          targ match
            case _: TypeBounds => // TODO: fix
              rec(arrayDims + 1, ObjectType)
            case targ: Type =>
              rec(arrayDims + 1, targ)
        case AppliedType(tycon, _) =>
          rec(arrayDims, tycon)
        case tpe: Symbolic =>
          tpe.resolveToSymbol match
            case cls: ClassSymbol =>
              cls.erasedName.toTermName match
                case SuffixedName(NameTags.OBJECTCLASS, full) => specialise(arrayDims, full).withObjectSuffix
                case full                                     => specialise(arrayDims, full)
            case sym => // TODO: abstract types
              throw IllegalStateException(s"Cannot erase symbolic type $tpe, with symbol $sym")
        case tpe =>
          throw IllegalStateException(s"Cannot erase $tpe")

      tpe match
        case _: ExprType => tpnme.scalaFunction0
        case _           => rec(0, tpe).toTypeName
  }

  abstract class Type {

    final def paramInfos: List[Type] = this match
      case tpe: MethodType => tpe.paramTypes
      case tpe             => Nil

    final def tparamBounds: List[TypeBounds] = this match
      case tpe: PolyType => tpe.paramTypeBounds
      case tpe           => Nil

    final def tparamRefs: List[TypeParamRef] = this match
      case tpe: PolyType => tpe.refs
      case tpe           => Nil

    final def resultType: Type = this match
      case tpe: MethodType => tpe.resType
      case tpe: PolyType   => tpe.resType
      case tpe: ExprType   => tpe.resType
      case tpe: TypeLambda => tpe.resType
      case tpe             => NoType

    final def termSymbol(using BaseContext): Symbol = this match
      case tpe: TermRef        => tpe.resolveToSymbol
      case tpe: PackageRef     => tpe.resolveToSymbol
      case tpe: PackageTypeRef => tpe.resolveToSymbol
      case _                   => NoSymbol

    final def widenOverloads(using BaseContext): Type =
      this.widen match
        case tp: TermRef => tp.underlying.widenOverloads
        case tp          => tp

    /** remove singleton types, ExprTypes and AnnotatedTypes */
    final def widen(using BaseContext): Type = this match
      case _: TypeRef | _: MethodType | _: PolyType => this // fast path for most frequent cases
      case tp: TermRef => // fast path for next most frequent case
        if tp.isOverloaded then tp else tp.underlying.widen
      case tp: SingletonType => tp.underlying.widen
      case tp: ExprType      => tp.resType.widen
      case tp: AnnotatedType => tp.typ.widen
      case tp: RefinedType   => tp.parent.widen
      case tp                => tp

    final def isRef(sym: Symbol)(using BaseContext): Boolean =
      this match {
        case tpe: NamedType   => tpe.resolveToSymbol == sym
        case tpe: AppliedType => tpe.underlying.isRef(sym)
        case tpe: ExprType    => tpe.underlying.isRef(sym)
        case _                => false // todo: add ProxyType (need to fill in implementations of underlying)
      }

    final def isOfClass(sym: Symbol)(using BaseContext): Boolean =
      this match {
        case tpe: TermRef =>
          tpe.underlying.isOfClass(sym)
        case tpe: ConstantType =>
          tpe.underlying.isOfClass(sym)
        case _ =>
          this.isRef(sym)
      }

    final def select(sym: Symbol)(using BaseContext): Type =
      NamedType(this, sym) // dotc also calls reduceProjection here, should we do it?
  }

  private def scalaPackage: PackageRef = PackageRef(nme.scalaPackageName)

  private def javalangPackage: PackageRef = PackageRef(nme.javalangPackageName)

  private def scalaDot(name: TypeName): TypeRef =
    TypeRef(scalaPackage, name)

  private def javalangDot(name: TypeName): Type =
    TypeRef(javalangPackage, name)

  def AnyType: Type = scalaDot(tpnme.Any)
  def NothingType: Type = scalaDot(tpnme.Nothing)
  def NullType: Type = scalaDot(tpnme.Null)

  def ArrayTypeUnapplied: TypeRef = scalaDot(tpnme.Array)
  def ArrayTypeOf(tpe: Type): AppliedType = AppliedType(ArrayTypeUnapplied, List(tpe))

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
    def underlying(using BaseContext): Type
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
    def isOverloaded(using BaseContext): Boolean = false
  }

  trait PathType extends TypeProxy with ValueType {
    final def select(name: Name): NamedType =
      if name.isTermName then TermRef(this, name)
      else TypeRef(this, name)
  }

  trait Symbolic {
    def resolveToSymbol(using BaseContext): Symbol
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
      else local
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
    override def resolveToSymbol(using BaseContext): Symbol = designator match {
      case sym: Symbol => sym
      case LookupIn(pre, name) =>
        val sym = TermRef(pre, name).resolveToSymbol
        designator = sym
        sym
      case Scala2ExternalSymRef(owner, path) =>
        val sym = path.foldLeft(owner) { (owner, name) =>
          owner.lookup(name).getOrElse {
            throw new SymbolLookupException(name, s"cannot find symbol $owner.$name")
          }
        }
        designator = sym
        sym
      case name: Name =>
        val prefixSym = prefix match {
          case NoPrefix =>
            throw new SymbolLookupException(name, "reference by name to a local symbol")
          case t: TermRef =>
            val underlyingType = t.underlying
            if (underlyingType == NoType)
              throw new ReferenceResolutionError(t, s"the term does not have a type")
            if (!underlyingType.isInstanceOf[Symbolic])
              throw new ReferenceResolutionError(
                t,
                s"only references to terms, whose type is a combination of typeref, termref and thistype, are supported. Got type $underlyingType"
              )
            underlyingType.asInstanceOf[Symbolic].resolveToSymbol
          case other: Symbolic => other.resolveToSymbol
          case prefix =>
            throw new SymbolLookupException(name, s"unexpected prefix type $prefix")
        }
        val sym = {
          prefixSym match
            case declaring: DeclaringSymbol =>
              val candidate = declaring.getDecl(name)
              candidate.getOrElse {
                val msg = this match
                  case TermRef(_, name: SignedName) if declaring.memberIsOverloaded(name) =>
                    def debugSig(sym: Symbol): String = sym.signature match {
                      case Some(sig) => sig.toDebugString
                      case None      => "<Not A Method>"
                    }
                    val debugQueried = name.sig.toDebugString
                    val debugCandidates = declaring.memberOverloads(name).map(debugSig).mkString("\n-  ", "\n-  ", "")
                    s"could not resolve overload:\nQueried:\n- $debugQueried\nPossible signatures:$debugCandidates"
                  case _ =>
                    s"not a member of $prefixSym"
                throw SymbolLookupException(name, msg)
              }
            case _ =>
              throw SymbolLookupException(name, s"$prefixSym is not a package or class")
        }
        designator = sym
        sym
    }
  }

  object NamedType {
    private def isType(designator: Designator): Boolean = designator match
      case designator: Symbol               => designator.isType
      case designator: Name                 => designator.isTypeName
      case designator: LookupIn             => false // always a SignedName, which is a TermName by construction
      case designator: Scala2ExternalSymRef => designator.name.isTypeName

    def apply(prefix: Type, designator: Designator)(using BaseContext): NamedType =
      if (isType(designator)) TypeRef(prefix, designator)
      else TermRef(prefix, designator)

    def apply(prefix: Type, sym: Symbol)(using BaseContext): NamedType =
      if (sym.isType) TypeRef(prefix, sym)
      else TermRef(prefix, sym)

    def apply(prefix: Type, name: Name)(using BaseContext): NamedType =
      if (name.isTypeName) TypeRef(prefix, name)
      else TermRef(prefix, name)
  }

  /** A reference to an implicit definition. This can be either a TermRef or a
    *  Implicits.RenamedImplicitRef.
    */
  trait ImplicitRef {
    def implicitName: TermName
    def underlyingRef: TermRef
  }

  abstract class SymResolutionProblem(msg: String, cause: Throwable | Null) extends Exception(msg, cause):
    def this(msg: String) = this(msg, null)

  class CyclicReference(val kind: String) extends Exception(s"cyclic evaluation of $kind")
  class NonMethodReference(val kind: String) extends Exception(s"reference to non method type in $kind")

  class ReferenceResolutionError(val ref: TermRef, explanation: String, cause: Throwable | Null)
      extends SymResolutionProblem(
        ReferenceResolutionError.addExplanation(s"Could not compute type of the term, referenced by $ref", explanation),
        cause
      ):
    def this(ref: TermRef, explanation: String) = this(ref, explanation, null)
    def this(ref: TermRef) = this(ref, "")
  end ReferenceResolutionError

  object ReferenceResolutionError {
    def unapply(e: ReferenceResolutionError): Option[TermRef] = Some(e.ref)

    def addExplanation(msg: String, explanation: String): String =
      if (explanation.isEmpty) msg else s"$msg: $explanation"
  }

  /** The singleton type for path prefix#myDesignator. */
  case class TermRef(override val prefix: Type, var myDesignator: Designator)
      extends NamedType
      with SingletonType
      with ImplicitRef {

    type ThisType = TermRef
    type ThisName = TermName

    override def designator: Designator = myDesignator

    override protected def designator_=(d: Designator): Unit = myDesignator = d

    override def underlying(using ctx: BaseContext): Type = {
      val termSymbol = resolveToSymbol
      try {
        termSymbol.declaredType
      } catch {
        case e =>
          val msg = e.getMessage
          throw new ReferenceResolutionError(this, if msg == null then "" else msg, e)
      }
    }

    override def isOverloaded(using BaseContext): Boolean =
      myDesignator match
        case LookupIn(pre, ref) =>
          pre.resolveToSymbol.memberIsOverloaded(ref)
        case _ => false

    def implicitName: TermName = name

    def underlyingRef: TermRef = this
  }

  class PackageRef(val packageName: TermName) extends NamedType with SingletonType {
    private var packageSymbol: PackageClassSymbol | Null = null

    def this(packageSym: PackageClassSymbol) =
      this(packageSym.name.toTermName)
      packageSymbol = packageSym

    override def designator: Designator =
      val pkgOpt = packageSymbol
      if pkgOpt == null then packageName else pkgOpt

    override protected def designator_=(d: Designator): Unit = throw UnsupportedOperationException(
      s"Can't assign designator of a package"
    )

    override def underlying(using BaseContext): Type = ???

    // TODO: root package?
    override val prefix: Type = NoType

    override def resolveToSymbol(using BaseContext): PackageClassSymbol = {
      val local = packageSymbol
      if (local == null) {
        def searchPkg = defn.RootPackage.findPackageSymbol(packageName)
        val resolved = searchPkg.getOrElse(throw new SymbolLookupException(packageName))
        packageSymbol = resolved
        resolved
      } else local
    }

    override def toString: String = s"PackageRef($packageName)"
  }

  object PackageRef {
    def unapply(r: PackageRef): Option[Name] = Some(r.packageName)
  }

  case class TypeRef(override val prefix: Type, private var myDesignator: Designator) extends NamedType {

    type ThisType = TypeRef
    type ThisName = TypeName

    override def designator: Designator = myDesignator

    override protected def designator_=(d: Designator): Unit = myDesignator = d

    override def underlying(using BaseContext): Type = ???
  }

  case object NoPrefix extends Type

  class PackageTypeRef(packageName: TermName) extends TypeRef(NoPrefix, packageName.toTypeName) {
    private val packageRef = PackageRef(packageName)

    override def resolveToSymbol(using BaseContext): Symbol = packageRef.resolveToSymbol
  }

  case class ThisType(tref: TypeRef) extends PathType with SingletonType with Symbolic {
    override def underlying(using BaseContext): Type = ???

    override def resolveToSymbol(using BaseContext): Symbol = tref.resolveToSymbol
  }

  /** A constant type with single `value`. */
  case class ConstantType(value: Constant) extends TypeProxy with SingletonType {
    override def underlying(using BaseContext): Type =
      value.wideType
  }

  /** A type application `C[T_1, ..., T_n]`
    * Typebounds for wildcard application: C[_], C[?]
    */
  case class AppliedType(tycon: Type, args: List[Type | TypeBounds]) extends TypeProxy with ValueType {
    override def underlying(using BaseContext): Type = tycon
  }

  /** A by-name parameter type of the form `=> T`, or the type of a method with no parameter list. */
  case class ExprType(resType: Type) extends TypeProxy with MethodicType {
    override def underlying(using BaseContext): Type = resType
  }

  case class MethodType(paramNames: List[TermName], paramTypes: List[Type], resType: Type) extends MethodicType

  final class PolyType private (val paramNames: List[TypeName])(
    @constructorOnly boundsRest: Binders => List[TypeBounds],
    @constructorOnly resultRest: Binders => Type
  ) extends MethodicType
      with Binders {
    private var evaluating: Boolean = false
    private val myBounds: List[TypeBounds] =
      evaluating = true
      boundsRest(this: @unchecked) // safe as long as `boundsRest` does not access bounds or result
    private val myRes: Type =
      resultRest(this: @unchecked) // safe as long as `resultRest` does not access bounds or result
        .andThen {
          evaluating = false
        }

    def paramTypeBounds: List[TypeBounds] =
      if evaluating then throw CyclicReference(s"polymorphic method [$paramNames]=>???")
      else myBounds

    def resType: Type =
      if evaluating then throw CyclicReference(s"polymorphic method [$paramNames]=>???")
      else myRes

    override def toString: String =
      if evaluating then s"PolyType($paramNames)(<evaluating>...)"
      else s"PolyType($paramNames)($myBounds, $myRes)"
  }

  object PolyType:
    def apply(paramNames: List[TypeName], paramTypeBounds: List[TypeBounds], resultType: Type): PolyType =
      new PolyType(paramNames)(_ => paramTypeBounds, _ => resultType)

    def rec(
      paramNames: List[TypeName]
    )(boundsRest: Binders => List[TypeBounds], resultRest: Binders => Type): PolyType =
      new PolyType(paramNames)(boundsRest, resultRest)

    def unapply(tpe: PolyType): (List[TypeName], List[TypeBounds], Type) =
      (tpe.paramNames, tpe.paramTypeBounds, tpe.resultType)

  /** Encapsulates the binders associated with a TypeParamRef. */
  sealed trait Binders:
    def lookupRef(name: Name): Option[Type] = (name, this) match
      case (tname: TypeName, hk: TypeLambda) =>
        hk.params.indexWhere(_.name == tname) match
          case -1  => None
          case idx => Some(newRef(idx))

      case (tname: TypeName, pt: PolyType) =>
        pt.paramNames.indexWhere(_ == tname) match
          case -1  => None
          case idx => Some(newRef(idx))

      case _ => None

    def newRef(idx: Int): TypeParamRef = TypeParamRef(this, idx)

    def refs: List[TypeParamRef] = this match
      case hk: TypeLambda => hk.params.indices.map(newRef).toList
      case pt: PolyType   => pt.paramNames.indices.map(newRef).toList

  case class TypeLambda(params: List[TypeParam])(@constructorOnly rest: Binders => Type)
      extends TypeProxy
      with TermType
      with Binders {
    private var evaluating: Boolean = false
    private val myResult: Type =
      evaluating = true
      rest(this: @unchecked /* safe as long as `rest` does not call `resultType` */ ).andThen { evaluating = false }

    def resType: Type =
      if evaluating then throw CyclicReference(s"type lambda [$params] =>> ???")
      else myResult

    override def underlying(using BaseContext): Type = ???

    override def toString: String =
      if evaluating then s"TypeLambda($params)(<evaluating>)"
      else s"TypeLambda($params)($myResult)"
  }

  case class TypeParamRef(binders: Binders, num: Int) extends TypeProxy with ValueType {
    override def underlying(using BaseContext): Type = ???

    def paramName: TypeName = binders match
      case hk: TypeLambda => hk.params(num).name
      case pt: PolyType   => pt.paramNames(num)

    def bounds(using BaseContext): TypeBounds = binders match
      case hk: TypeLambda => hk.params(num).computeDeclarationTypeBounds()
      case pt: PolyType   => pt.paramTypeBounds(num)

    override def toString: String = paramName.toString
  }

  /** typ @ annot */
  case class AnnotatedType(typ: Type, annotation: Tree) extends TypeProxy with ValueType {
    override def underlying(using BaseContext): Type = typ
  }

  /** A refined type parent { refinement }
    *  @param parent      The type being refined
    *  @param refinedName The name of the refinement declaration
    *  @param refinedInfo The info of the refinement declaration
    */
  case class RefinedType(parent: Type, refinedName: Name, refinedInfo: TypeBounds) extends TypeProxy with ValueType {
    override def underlying(using BaseContext): Type = parent
  }

  trait TypeBounds(val low: Type, val high: Type)

  case class RealTypeBounds(override val low: Type, override val high: Type) extends TypeBounds(low, high)

  case class TypeAlias(alias: Type) extends TypeProxy with TypeBounds(alias, alias) {
    override def underlying(using BaseContext): Type = alias
  }

  case class BoundedType(bounds: TypeBounds, alias: Type) extends Type

  case class NamedTypeBounds(name: TypeName, bounds: TypeBounds) extends Type

  // ----- Ground Types -------------------------------------------------

  case class OrType(first: Type, second: Type) extends GroundType with ValueType

  case class AndType(first: Type, second: Type) extends GroundType with ValueType

  case class ClassType(cls: ClassSymbol, rawParents: Type) extends GroundType

  case object NoType extends GroundType
}
