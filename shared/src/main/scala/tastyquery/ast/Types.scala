package tastyquery.ast

import tastyquery.ast.Constants.Constant
import tastyquery.ast.Names.{Name, TermName, TypeName}
import tastyquery.ast.Symbols.Symbol
import tastyquery.ast.Trees.{Tree, TypeParam}

object Types {
  type Designator = Symbol | Name

  abstract class Type

  // ----- Type categories ----------------------------------------------

  // Every type is expected to inherit either TypeProxy or GroundType.

  /**
   * Type proxies.
   * Each implementation is expected to redefine the `underlying` method.
   */
  abstract class TypeProxy extends Type {

    /** The type to which this proxy forwards operations. */
    def underlying: Type
  }

  /** Non-proxy types */
  abstract class GroundType extends Type {}

  // ----- Marker traits ------------------------------------------------

  /**
   * A marker trait for types that apply only to term symbols or that
   * represent higher-kinded types.
   */
  trait TermType extends Type

  /** A marker trait for types that can be types of values or prototypes of value types */
  trait ValueTypeOrProto extends TermType

  /** A marker trait for types that can be types of values or that are higher-kinded */
  trait ValueType extends ValueTypeOrProto

  /**
   * A marker trait for types that are guaranteed to contain only a
   * single non-null value (they might contain null in addition).
   */
  trait SingletonType extends TypeProxy with ValueType {
    def isOverloaded: Boolean = false
  }

  // ----- Type Proxies -------------------------------------------------

  abstract class NamedType extends TypeProxy with ValueType {
    self =>

    type ThisType >: this.type <: NamedType
    type ThisName <: Name

    val prefix: Type

    def designator: Designator

    protected def designator_=(d: Designator): Unit

    private var myName: Name = null

    def isType: Boolean = isInstanceOf[TypeRef]

    def isTerm: Boolean = isInstanceOf[TermRef]

    /**
     * If designator is a name, this name. Otherwise, the original name
     * of the designator symbol.
     */
    final def name: ThisName = {
      if (myName == null) myName = computeName
      myName.asInstanceOf[ThisName]
    }

    private def computeName: Name = designator match {
      case name: Name  => name
      case sym: Symbol => sym.name
    }
  }

  /**
   * A reference to an implicit definition. This can be either a TermRef or a
   *  Implicits.RenamedImplicitRef.
   */
  trait ImplicitRef {
    def implicitName: TermName
    def underlyingRef: TermRef
  }

  /**
   * The singleton type for path prefix#myDesignator.
   */
  case class TermRef(override val prefix: Type, var myDesignator: Designator)
      extends NamedType
      with SingletonType
      with ImplicitRef {

    type ThisType = TermRef
    type ThisName = TermName

    override def designator: Designator = myDesignator

    override protected def designator_=(d: Designator): Unit = myDesignator = d

    override def underlying: Type = ???

    override def isOverloaded: Boolean = ???

    def implicitName: TermName = name

    def underlyingRef: TermRef = this
  }

  case class TypeRef(override val prefix: Type, private var myDesignator: Designator) extends NamedType {

    type ThisType = TypeRef
    type ThisName = TypeName

    override def designator: Designator = myDesignator

    override protected def designator_=(d: Designator): Unit = myDesignator = d

    override def underlying: Type = ???
  }

  case object NoPrefix extends Type

  // TODO: store the package type symbol
  class PackageTypeRef(packageName: Name) extends TypeRef(NoPrefix, packageName)

  case class ThisType(tref: TypeRef) extends TypeProxy with SingletonType {
    override def underlying: Type = ???
  }

  /** A constant type with single `value`. */
  case class ConstantType(value: Constant) extends TypeProxy with SingletonType {
    override def underlying: Type = ???
  }

  /** A type application `C[T_1, ..., T_n]` */
  case class AppliedType(tycon: Type, args: List[Type]) extends TypeProxy with ValueType {
    override def underlying: Type = tycon
  }

  case class TypeLambda(params: List[TypeParam], resultTypeCtor: TypeLambda => Type) extends TypeProxy with TermType {
    val resultType = resultTypeCtor(this)

    override def underlying: Type = ???

    override def toString: String = s"TypeLambda($params, $resultType)"
  }

  case class TypeParamRef(binder: TypeLambda, num: Int) extends TypeProxy with ValueType {
    override def underlying: Type = ???

    override def toString: String = binder.params(num).name.toString
  }

  /** typ @ annot */
  case class AnnotatedType(typ: Type, annotation: Tree) extends TypeProxy with ValueType {
    override def underlying: Type = typ
  }

  // A marker for Types or components which are not yet constructed correctly
  case object DummyType extends Type

  trait TypeBounds(low: Type, high: Type)

  case class RealTypeBounds(low: Type, high: Type) extends TypeBounds(low, high)

  case class TypeAlias(alias: Type) extends TypeProxy with TypeBounds(alias, alias) {
    override def underlying: Type = alias
  }

  // ----- Ground Types -------------------------------------------------

  case class OrType(first: Type, second: Type) extends GroundType with ValueType

  case class AndType(first: Type, second: Type) extends GroundType with ValueType
}
