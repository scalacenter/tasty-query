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
  type Designator = Symbol | Name | LookupIn

  case class LookupIn(pre: TypeRef, sel: SignedName)

  abstract class Type {

    /** remove singleton types, ExprTypes and AnnotatedTypes */
    final def widen(using BaseContext): Type = this match
      case _: TypeRef | _: MethodType | _: PolyType => this // fast path for most frequent cases
      case tp: TermRef => // fast path for next most frequent case
        if tp.isOverloaded then tp else tp.underlying.widen
      case tp: SingletonType   => tp.underlying.widen
      case tp: ExprType        => tp.resType.widen
      case tp: AnnotatedType   => tp.typ.widen
      case tp: Application     => tp.underlying.widen
      case tp: TypeApplication => tp.underlying.widen
      case tp                  => tp

    final def isRef(sym: Symbol)(using BaseContext): Boolean =
      this match {
        case tpe: NamedType       => tpe.resolveToSymbol == sym
        case tpe: Application     => tpe.underlying.isRef(sym)
        case tpe: TypeApplication => tpe.underlying.isRef(sym)
        case _                    => false // todo: add ProxyType (need to fill in implementations of underlying)
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
  }

  private def scalaPackage: PackageRef = PackageRef(nme.scalaPackageName)

  private def javalangPackage: PackageRef = PackageRef(nme.javalangPackageName)

  private def scalaDot(name: TypeName): Type =
    TypeRef(scalaPackage, name)

  private def javalangDot(name: TypeName): Type =
    TypeRef(javalangPackage, name)

  def AnyType: Type = scalaDot(tpnme.Any)
  def NothingType: Type = scalaDot(tpnme.Nothing)
  def NullType: Type = scalaDot(tpnme.Null)

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
  def ClassTypeOf(cls: Type): Type = AppliedType(javalangDot(tpnme.Class), List(cls))

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

  trait Symbolic {
    def resolveToSymbol(using BaseContext): Symbol
  }

  // ----- Type Proxies -------------------------------------------------

  private[tastyquery] def MethodApplication(funTpe: Type, args: List[Type]): Type = Application(funTpe, args)
  private[tastyquery] def MethodTypeApplication(funTpe: Type, args: List[Type]): Type = TypeApplication(funTpe, args)

  private class Application(funTpe: Type, args: List[Type]) extends TypeProxy with ValueType {
    def underlying(using BaseContext): Type =
      funTpe.widen match
        case funTpe: MethodType =>
          // todo: check that the arguments correspond to the parameters, substitute when dependent
          funTpe.resultType
        case tpe =>
          throw NonMethodReference(s"application of args ${args.mkString} to $tpe")
  }

  private class TypeApplication(funTpe: Type, args: List[Type]) extends TypeProxy with ValueType {
    def underlying(using BaseContext): Type =
      funTpe.widen match
        case funTpe: PolyType =>
          funTpe.resultType // todo: check that the arguments correspond to the parameters
        case tpe =>
          throw NonMethodReference(s"type application of args ${args.mkString} to $tpe")
  }

  abstract class NamedType extends TypeProxy with ValueType with Symbolic {
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
      case name: Name       => name
      case sym: Symbol      => sym.name
      case LookupIn(_, sel) => sel
    }).asInstanceOf[ThisName]

    def selectIn(name: SignedName, in: TypeRef): TermRef =
      TermRef(this, LookupIn(in, name))

    def select(name: Name): NamedType =
      if name.isTermName then TermRef(this, name)
      else TypeRef(this, name)

    // overridden in package references
    override def resolveToSymbol(using BaseContext): Symbol = designator match {
      case sym: Symbol => sym
      case LookupIn(pre, name) =>
        val sym = TermRef(pre, name).resolveToSymbol
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
          val symOption = prefixSym match {
            case declaring: DeclaringSymbol =>
              declaring.getDecl(name)
            case _ =>
              throw SymbolLookupException(name, s"$prefixSym is not a package or class")
          }
          symOption.getOrElse(throw new SymbolLookupException(name, s"not a member of $prefixSym"))
        }
        designator = sym
        sym
    }
  }

  /** A reference to an implicit definition. This can be either a TermRef or a
    *  Implicits.RenamedImplicitRef.
    */
  trait ImplicitRef {
    def implicitName: TermName
    def underlyingRef: TermRef
  }

  class CyclicReference(val kind: String) extends Exception(s"cyclic evaluation of $kind")
  class NonMethodReference(val kind: String) extends Exception(s"reference to non method type in $kind")

  class ReferenceResolutionError(val ref: TermRef, explanation: String, cause: Throwable | Null)
      extends RuntimeException(
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
    var packageSymbol: PackageClassSymbol | Null = null

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

  case class ThisType(tref: TypeRef) extends TypeProxy with SingletonType with Symbolic {
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

  case class MethodType(paramNames: List[TermName], paramTypes: List[Type], resultType: Type) extends MethodicType

  case class PolyType(paramNames: List[TypeName], paramTypeBounds: List[TypeBounds], resultType: Type)
      extends MethodicType

  /** Encapsulates the binders associated with a TypeParamRef. */
  opaque type Binders = TypeLambda

  case class TypeLambda(params: List[TypeParam])(@constructorOnly rest: Binders => Type)
      extends TypeProxy
      with TermType {
    private var evaluating: Boolean = false
    private val myResult: Type =
      evaluating = true
      rest(this: @unchecked /* safe as long as `rest` does not call `resultType` */ ).andThen { evaluating = false }

    def resultType: Type =
      if evaluating then throw CyclicReference(s"type lambda [$params] =>> ???")
      else myResult

    override def underlying(using BaseContext): Type = ???

    override def toString: String =
      if evaluating then s"TypeLambda($params)(<evaluating>)"
      else s"TypeLambda($params)($myResult)"
  }

  case class TypeParamRef(binders: Binders, num: Int) extends TypeProxy with ValueType {
    override def underlying(using BaseContext): Type = ???

    def paramName = binders.params(num).name

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

  trait TypeBounds(low: Type, high: Type)

  case class RealTypeBounds(low: Type, high: Type) extends TypeBounds(low, high)

  case class TypeAlias(alias: Type) extends TypeProxy with TypeBounds(alias, alias) {
    override def underlying(using BaseContext): Type = alias
  }

  case class BoundedType(bounds: TypeBounds, alias: Type) extends Type

  case class NamedTypeBounds(name: TypeName, bounds: TypeBounds) extends Type

  // ----- Ground Types -------------------------------------------------

  case class OrType(first: Type, second: Type) extends GroundType with ValueType

  case class AndType(first: Type, second: Type) extends GroundType with ValueType

  case object NoType extends GroundType
}
