package tastyquery

import java.util.concurrent.ConcurrentHashMap

import dotty.tools.tasty.TastyFormat.NameTags

import scala.reflect.NameTransformer

import scala.annotation.targetName

import scala.jdk.CollectionConverters.*

import tastyquery.Signatures.Signature

import Names.SimpleName

private[tastyquery] object NameCache {

  // A map from the name to itself. Used to keep only one instance of SimpleName by underlying String
  private val nameTable: scala.collection.concurrent.Map[SimpleName, SimpleName] =
    new ConcurrentHashMap[SimpleName, SimpleName]().asScala

  private[tastyquery] def cache(newName: SimpleName): SimpleName = {
    val oldName = nameTable.putIfAbsent(newName, newName)
    oldName.getOrElse(newName)
  }

}

object Names {

  given Ordering[SimpleName] = Ordering.by(_.name)

  object str {
    val topLevelSuffix = "$package"
    val SuperAccessorPrefix: String = "super$"
    val InlineAccessorPrefix: String = "inline$"
    val BodyRetainerSuffix: String = "$retainedBody"
  }

  object attr {
    val TASTY = termName("TASTY")
    val Scala = termName("Scala")
    val ScalaSig = termName("ScalaSig")
    val InnerClasses = termName("InnerClasses")
    val RuntimeVisibleAnnotations = termName("RuntimeVisibleAnnotations") // RetentionPolicy.RUNTIME
    val RuntimeInvisibleAnnotations = termName("RuntimeInvisibleAnnotations") // RetentionPolicy.CLASS
    val Signature = termName("Signature")
  }

  object annot {
    val ScalaSignature = termName("Lscala/reflect/ScalaSignature;")
    val ScalaLongSignature = termName("Lscala/reflect/ScalaLongSignature;")
  }

  object nme {

    /** The term name represented by the empty string */
    val EmptySimpleName: SimpleName = termName("")
    val EmptyTermName: SimpleName = EmptySimpleName
    val EmptyTypeName: TypeName = EmptyTermName.toTypeName
    val RootName: SimpleName = termName("<root>")
    val RootPackageName: SimpleName = termName("_root_")
    val EmptyPackageName: SimpleName = termName("<empty>")
    val Constructor: SimpleName = termName("<init>")
    val Wildcard: SimpleName = termName("_")
    val WildcardSequence: SimpleName = termName("_*")
    val RefinementClass = typeName("<refinement>")

    val specialOpsPackageName: SimpleName = termName("<special-ops>")
    val scalaPackageName: SimpleName = termName("scala")
    val javaPackageName: SimpleName = termName("java")
    val langPackageName: SimpleName = termName("lang")
    val runtimePackageName: SimpleName = termName("runtime")

    val EmptyTuple: SimpleName = termName("EmptyTuple")

    val m_== : SimpleName = termName("==")
    val m_!= : SimpleName = termName("!=")
    val m_## : SimpleName = termName("##")
    val m_equals: SimpleName = termName("equals")
    val m_hashCode: SimpleName = termName("hashCode")
    val m_toString: SimpleName = termName("toString")
    val m_isInstanceOf: SimpleName = termName("isInstanceOf")
    val m_asInstanceOf: SimpleName = termName("asInstanceOf")
    val m_getClass: SimpleName = termName("getClass")

    val m_eq: SimpleName = termName("eq")
    val m_ne: SimpleName = termName("ne")
    val m_synchronized: SimpleName = termName("synchronized")

    val m_+ : SimpleName = termName("+")

    val m_apply: SimpleName = termName("apply")
  }

  object tpnme {
    val Any: TypeName = typeName("Any")
    val AnyVal: TypeName = typeName("AnyVal")
    val Nothing: TypeName = typeName("Nothing")
    val Null: TypeName = typeName("Null")

    val Array: TypeName = typeName("Array")
    val Seq: TypeName = typeName("Seq")

    val Unit: TypeName = typeName("Unit")
    val Boolean: TypeName = typeName("Boolean")
    val Char: TypeName = typeName("Char")
    val Byte: TypeName = typeName("Byte")
    val Short: TypeName = typeName("Short")
    val Int: TypeName = typeName("Int")
    val Long: TypeName = typeName("Long")
    val Float: TypeName = typeName("Float")
    val Double: TypeName = typeName("Double")

    val String: TypeName = typeName("String")
    val Class: TypeName = typeName("Class")
    val Object: TypeName = typeName("Object")

    val Product: TypeName = typeName("Product")
    val Tuple: TypeName = typeName("Tuple")
    val NonEmptyTuple: TypeName = typeName("NonEmptyTuple")
    val TupleCons: TypeName = typeName("*:")
    val Enum: TypeName = typeName("Enum")

    @deprecated("you probably meant the term name `nme.EmptyTuple` instead", since = "0.8.3")
    val EmptyTuple: TypeName = typeName("EmptyTuple")

    val RefinedClassMagic: TypeName = typeName("<refinement>")
    val ByNameParamClassMagic: TypeName = typeName("<byname>")
    val RepeatedParamClassMagic: TypeName = typeName("<repeated>")
    val FromJavaObjectAliasMagic: TypeName = typeName("<FromJavaObject>")

    val scala2PackageObjectClass: TypeName = termName("package").withObjectSuffix.toTypeName

    private[tastyquery] val runtimeNothing: TypeName = typeName("Nothing$")
    private[tastyquery] val runtimeBoxedUnit: TypeName = typeName("BoxedUnit")

    private[tastyquery] val internalRepeatedAnnot: TypeName = typeName("Repeated")

    private[tastyquery] val scala2LocalChild: TypeName = typeName("<local child>")
    private[tastyquery] val scala2ByName: TypeName = typeName("<byname>")

    private[tastyquery] val PredefModule: TypeName = moduleClassName("Predef")

    private[tastyquery] val MethodHandle: TypeName = typeName("MethodHandle")
    private[tastyquery] val VarHandle: TypeName = typeName("VarHandle")
  }

  /** Create a type name from a string */
  def typeName(s: String): TypeName =
    termName(s).toTypeName

  /** Create a term name from a string.
    * See `sliceToTermName` in `Decorators` for a more efficient version
    * which however requires a Context for its operation.
    */
  def termName(s: String): SimpleName =
    NameCache.cache(SimpleName(s))

  /** Creates a type name for a module class from a string. */
  def moduleClassName(s: String): TypeName =
    termName(s).withObjectSuffix.toTypeName

  sealed abstract class Name derives CanEqual {

    /** This name converted to a type name */
    def toTypeName: TypeName

    /** This name converted to a term name */
    def toTermName: TermName

    /** This name downcasted to a simple term name */
    def asSimpleName: SimpleName

    final def isTypeName: Boolean = this.isInstanceOf[TypeName]
    final def isTermName: Boolean = !isTypeName

    def isEmpty: Boolean

    def toDebugString: String = toString

    def decode: Name = this match
      case name: SimpleName                         => termName(NameTransformer.decode(name.name))
      case SuffixedName(NameTags.OBJECTCLASS, name) => name.decode.toTermName.withObjectSuffix
      case name: TypeName                           => name.toTermName.decode.toTypeName
      case _                                        => this // TODO: add more cases
  }

  abstract class TermName extends Name {
    def tag: Int

    override def toTermName: TermName = this

    override lazy val toTypeName: TypeName = TypeName(this)

    def withObjectSuffix: SuffixedName = SuffixedName(NameTags.OBJECTCLASS, this)
    def stripObjectSuffix: TermName = this match
      case SuffixedName(NameTags.OBJECTCLASS, rest) => rest
      case _                                        => this
  }

  final case class SimpleName(name: String) extends TermName {
    override def tag: Int = NameTags.UTF8

    override def asSimpleName: SimpleName = this

    override def isEmpty: Boolean = name.length == 0

    override def toString: String = name

    def prepend(s: String): SimpleName =
      termName(s + name)

    def append(s: String): SimpleName =
      termName(name + s)

    private[tastyquery] def isPackageObjectName: Boolean =
      name == "package" || name.endsWith(str.topLevelSuffix)
  }

  abstract class DerivedName(val underlying: TermName) extends TermName {
    override def asSimpleName: SimpleName = throw new UnsupportedOperationException(
      s"$this is not a simple " +
        s"name"
    )

    override def isEmpty: Boolean = false
  }

  final case class SignedName(override val underlying: TermName, sig: Signature, target: TermName)
      extends DerivedName(underlying) {
    override def tag: Int = NameTags.SIGNED

    override def toString: String = s"$underlying[with sig $sig @$target]"

    override def toDebugString: String =
      s"${underlying.toDebugString}[with sig ${sig.toDebugString} @${target.toDebugString}]"
  }

  object SignedName:
    def apply(underlying: TermName, sig: Signature): SignedName =
      SignedName(underlying, sig, underlying)
  end SignedName

  final case class ExpandedName(override val tag: Int, prefix: TermName, name: SimpleName) extends DerivedName(prefix) {
    def separator: String = tag match {
      case NameTags.EXPANDED     => "$$"
      case NameTags.EXPANDPREFIX => "$"
    }

    override def toDebugString: String =
      s"${prefix.toDebugString}[Expanded $separator $name]"

    override def toString: String = s"$prefix$separator$name"
  }

  final case class PrefixedName(override val tag: Int, override val underlying: TermName)
      extends DerivedName(underlying) {
    override def toString: String = tag match {
      case NameTags.SUPERACCESSOR  => s"super$underlying"
      case NameTags.INLINEACCESSOR => s"inline$underlying"
    }

    override def toDebugString: String = tag match
      case NameTags.SUPERACCESSOR  => s"<super:${underlying.toDebugString}>"
      case NameTags.INLINEACCESSOR => s"<inline:${underlying.toDebugString}>"
  }

  final case class SuffixedName(override val tag: Int, override val underlying: TermName)
      extends DerivedName(underlying) {
    override def toString: String = tag match {
      case NameTags.BODYRETAINER => s"<bodyretainer$underlying>" // probably wrong but print something without crashing
      case NameTags.OBJECTCLASS  => underlying.toString
    }

    override def toDebugString: String = tag match {
      case NameTags.BODYRETAINER => s"<bodyretainer:$underlying>"
      case NameTags.OBJECTCLASS  => s"${underlying.toDebugString}[$$]"
    }
  }

  abstract class NumberedName(underlying: TermName, num: Int) extends DerivedName(underlying)

  // TODO: factor out the separators
  final case class UniqueName(separator: String, override val underlying: TermName, num: Int)
      extends NumberedName(underlying, num) {
    override def tag: Int = NameTags.UNIQUE

    override def toString: String = s"$underlying$separator$num"

    override def toDebugString: String = s"${underlying.toDebugString}[unique $separator $num]"
  }

  // can't instantiate directly, might have to nest the other way
  final case class DefaultGetterName(override val underlying: TermName, num: Int)
      extends NumberedName(underlying, num) {
    override def tag: Int = NameTags.DEFAULTGETTER

    override def toString: String = s"$underlying$$default$$${num + 1}"

    override def toDebugString: String = s"${underlying.toDebugString}[default $num]"
  }

  final case class TypeName(override val toTermName: TermName) extends Name {
    override def toTypeName: TypeName = this

    override def asSimpleName: SimpleName = toTermName.asSimpleName

    override def isEmpty: Boolean = toTermName.isEmpty

    override def toString: String = toTermName.toString

    override def toDebugString: String = s"${toTermName.toDebugString}/T"

    def wrapsObjectName: Boolean = toTermName match
      case SuffixedName(NameTags.OBJECTCLASS, _) => true
      case _                                     => false

    def companionName: TypeName = toTermName match
      case SuffixedName(NameTags.OBJECTCLASS, clsName) => clsName.toTypeName
      case name                                        => name.withObjectSuffix.toTypeName

    def sourceObjectName: SimpleName = toTermName match
      case SuffixedName(NameTags.OBJECTCLASS, objName) => objName.asSimpleName
      case name                                        => name.asSimpleName

    private[tastyquery] def isPackageObjectClassName: Boolean =
      wrapsObjectName && toTermName.stripObjectSuffix.asSimpleName.isPackageObjectName
  }

  final case class FullyQualifiedName(path: List[Name]):
    override def toString(): String =
      path.mkString(".")

    def toDebugString: String =
      path.map(_.toDebugString).mkString(".")

    def select(name: Name): FullyQualifiedName = FullyQualifiedName(path :+ name)

    def mapLast(op: Name => Name): FullyQualifiedName =
      FullyQualifiedName(path.init :+ op(path.last))

    private[tastyquery] def sourceName: Name = path match
      case Nil  => nme.RootPackageName
      case path => path.last

    def mapLastOption(op: Name => Name): FullyQualifiedName =
      if path.isEmpty then this
      else mapLast(op)
  end FullyQualifiedName

  object FullyQualifiedName:
    val rootPackageName = FullyQualifiedName(Nil)
    val emptyPackageName = FullyQualifiedName(nme.EmptyPackageName :: Nil)
    val scalaPackageName = FullyQualifiedName(nme.scalaPackageName :: Nil)
    val javaLangPackageName = FullyQualifiedName(nme.javaPackageName :: nme.langPackageName :: Nil)
    val scalaRuntimePackageName = FullyQualifiedName(nme.scalaPackageName :: nme.runtimePackageName :: Nil)

    private[tastyquery] val scalaAnnotationInternalPackage =
      FullyQualifiedName(nme.scalaPackageName :: termName("annotation") :: termName("internal") :: Nil)
  end FullyQualifiedName
}
