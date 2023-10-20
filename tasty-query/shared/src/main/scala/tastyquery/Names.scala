package tastyquery

import java.util.concurrent.ConcurrentHashMap

import dotty.tools.tasty.TastyFormat.NameTags

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

    // For signatures
    private[tastyquery] val Nothing: SimpleName = termName("Nothing")
    private[tastyquery] val runtimeNothing: SimpleName = termName("Nothing$")

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
    val Wildcard: TypeName = typeName("_")

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
    def toDebugString: String = toString
  }

  sealed abstract class TermName extends Name {
    final lazy val toTypeName: TypeName = TypeName(this)
  }

  sealed trait SignatureNameItem extends TermName

  final case class SimpleName(name: String) extends TermName with SignatureNameItem {
    override def toString: String = name

    def prepend(s: String): SimpleName =
      termName(s + name)

    def append(s: String): SimpleName =
      termName(name + s)

    def withObjectSuffix: ObjectClassName = ObjectClassName(this)

    private[tastyquery] def isPackageObjectName: Boolean =
      name == "package" || name.endsWith(str.topLevelSuffix)
  }

  sealed abstract class DerivedName(val underlying: TermName) extends TermName

  final case class SignedName(override val underlying: TermName, sig: Signature, target: TermName)
      extends DerivedName(underlying) {
    override def toString: String = s"$underlying[with sig $sig @$target]"

    override def toDebugString: String =
      s"${underlying.toDebugString}[with sig ${sig.toDebugString} @${target.toDebugString}]"
  }

  object SignedName:
    def apply(underlying: TermName, sig: Signature): SignedName =
      SignedName(underlying, sig, underlying)
  end SignedName

  final case class ExpandedName(prefix: TermName, name: SimpleName) extends DerivedName(prefix) {
    override def toDebugString: String =
      s"${prefix.toDebugString}[Expanded $$$$ $name]"

    override def toString: String = s"$prefix$$$$$name"
  }

  final case class ExpandPrefixName(prefix: TermName, name: SimpleName) extends DerivedName(prefix) {
    override def toDebugString: String =
      s"${prefix.toDebugString}[ExpandPrefix $$ $name]"

    override def toString: String = s"$prefix$$$name"
  }

  final case class SuperAccessorName(override val underlying: TermName) extends DerivedName(underlying) {
    override def toString: String = s"super$underlying"

    override def toDebugString: String = s"<super:${underlying.toDebugString}>"
  }

  final case class InlineAccessorName(override val underlying: TermName) extends DerivedName(underlying) {
    override def toString: String = s"inline$underlying"

    override def toDebugString: String = s"<inline:${underlying.toDebugString}>"
  }

  final case class BodyRetainerName(override val underlying: TermName) extends DerivedName(underlying) {
    override def toString: String = s"<bodyretainer$underlying>" // probably wrong but print something without crashing

    override def toDebugString: String = s"<bodyretainer:$underlying>"
  }

  final case class ObjectClassName(override val underlying: SimpleName)
      extends DerivedName(underlying)
      with SignatureNameItem {
    override def toString: String = underlying.toString + "$"

    override def toDebugString: String = s"${underlying.toDebugString}[$$]"
  }

  // TODO: factor out the separators
  final case class UniqueName(separator: String, override val underlying: TermName, num: Int)
      extends DerivedName(underlying) {
    override def toString: String = s"$underlying$separator$num"

    override def toDebugString: String = s"${underlying.toDebugString}[unique $separator $num]"
  }

  // can't instantiate directly, might have to nest the other way
  final case class DefaultGetterName(override val underlying: TermName, num: Int) extends DerivedName(underlying) {
    override def toString: String = s"$underlying$$default$$${num + 1}"

    override def toDebugString: String = s"${underlying.toDebugString}[default $num]"
  }

  final case class TypeName(val toTermName: TermName) extends Name {
    override def toString: String = toTermName.toString

    override def toDebugString: String = s"${toTermName.toDebugString}/T"

    def wrapsObjectName: Boolean = toTermName.isInstanceOf[ObjectClassName]

    def companionName: TypeName = toTermName match
      case ObjectClassName(clsName) => clsName.toTypeName
      case name: SimpleName         => name.withObjectSuffix.toTypeName
      case _                        => throw IllegalArgumentException(s"Illegal class name $toDebugString")

    def sourceObjectName: SimpleName = toTermName match
      case ObjectClassName(objName) => objName
      case name: SimpleName         => name
      case _                        => throw IllegalArgumentException(s"Illegal class name $toDebugString")

    private[tastyquery] def isPackageObjectClassName: Boolean = toTermName match
      case ObjectClassName(objName) => objName.isPackageObjectName
      case _                        => false
  }

  final case class PackageFullName(path: List[SimpleName]):
    override def toString(): String =
      path.mkString(".")

    // for consistency with other name types, but it is always the same as toString() here
    def toDebugString: String =
      toString()

    def select(subPackage: SimpleName): PackageFullName =
      PackageFullName(path :+ subPackage)

    private[tastyquery] def simpleName: SimpleName = path match
      case Nil  => nme.RootPackageName
      case path => path.last
  end PackageFullName

  object PackageFullName:
    val rootPackageName = PackageFullName(Nil)
    val emptyPackageName = PackageFullName(nme.EmptyPackageName :: Nil)
    val scalaPackageName = PackageFullName(nme.scalaPackageName :: Nil)
    val javaLangPackageName = PackageFullName(nme.javaPackageName :: nme.langPackageName :: Nil)
    val scalaRuntimePackageName = PackageFullName(nme.scalaPackageName :: nme.runtimePackageName :: Nil)

    private[tastyquery] val scalaAnnotationInternalPackage =
      PackageFullName(nme.scalaPackageName :: termName("annotation") :: termName("internal") :: Nil)
  end PackageFullName

  final case class SignatureName(items: List[SignatureNameItem]):
    override def toString(): String =
      items.mkString(".")

    def toDebugString: String =
      items.map(_.toDebugString).mkString(".")

    def appendItem(item: SignatureNameItem): SignatureName =
      SignatureName(items :+ item)
  end SignatureName
}
