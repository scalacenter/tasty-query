package tastyquery

import java.util.concurrent.ConcurrentHashMap

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

  object nme {
    val EmptyTermName: SimpleName = termName("")
    val RootName: SimpleName = termName("<root>")
    val UserLandRootPackageName: SimpleName = termName("_root_")
    val EmptyPackageName: SimpleName = termName("<empty>")
    val Constructor: SimpleName = termName("<init>")
    val Wildcard: SimpleName = termName("_")
    val WildcardSequence: SimpleName = termName("_*")

    val specialOpsPackageName: SimpleName = termName("<special-ops>")
    val scalaPackageName: SimpleName = termName("scala")
    val javaPackageName: SimpleName = termName("java")
    val langPackageName: SimpleName = termName("lang")

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
    val m_unapply: SimpleName = termName("unapply")

    private[tastyquery] val m_macro: SimpleName = termName("macro")
  }

  object tpnme {
    val EmptyTypeName: SimpleTypeName = typeName("")
    val Wildcard: SimpleTypeName = typeName("_")

    val Any: SimpleTypeName = typeName("Any")
    val Matchable: SimpleTypeName = typeName("Matchable")
    val AnyVal: SimpleTypeName = typeName("AnyVal")
    val Nothing: SimpleTypeName = typeName("Nothing")
    val Null: SimpleTypeName = typeName("Null")

    val Array: SimpleTypeName = typeName("Array")
    val Seq: SimpleTypeName = typeName("Seq")

    val Unit: SimpleTypeName = typeName("Unit")
    val Boolean: SimpleTypeName = typeName("Boolean")
    val Char: SimpleTypeName = typeName("Char")
    val Byte: SimpleTypeName = typeName("Byte")
    val Short: SimpleTypeName = typeName("Short")
    val Int: SimpleTypeName = typeName("Int")
    val Long: SimpleTypeName = typeName("Long")
    val Float: SimpleTypeName = typeName("Float")
    val Double: SimpleTypeName = typeName("Double")

    val String: SimpleTypeName = typeName("String")
    val Class: SimpleTypeName = typeName("Class")
    val Object: SimpleTypeName = typeName("Object")

    val Product: SimpleTypeName = typeName("Product")
    val Tuple: SimpleTypeName = typeName("Tuple")
    val NonEmptyTuple: SimpleTypeName = typeName("NonEmptyTuple")
    val TupleCons: SimpleTypeName = typeName("*:")
    val Enum: SimpleTypeName = typeName("Enum")

    val PolyFunction: SimpleTypeName = typeName("PolyFunction")
    val Singleton: SimpleTypeName = typeName("Singleton")

    val RefinedClassMagic: SimpleTypeName = typeName("<refinement>")
    val RepeatedParamClassMagic: SimpleTypeName = typeName("<repeated>")
    val FromJavaObjectAliasMagic: SimpleTypeName = typeName("<FromJavaObject>")

    private[tastyquery] val internalRepeatedAnnot: SimpleTypeName = typeName("Repeated")

    private[tastyquery] val scala2LocalChild: SimpleTypeName = typeName("<local child>")
    private[tastyquery] val scala2ByName: SimpleTypeName = typeName("<byname>")

    private[tastyquery] val PredefModule: ObjectClassTypeName = moduleClassName("Predef")

    private[tastyquery] val MethodHandle: SimpleTypeName = typeName("MethodHandle")
    private[tastyquery] val VarHandle: SimpleTypeName = typeName("VarHandle")
  }

  /** Create a type name from a string */
  def typeName(s: String): SimpleTypeName =
    termName(s).toTypeName

  /** Create a term name from a string.
    * See `sliceToTermName` in `Decorators` for a more efficient version
    * which however requires a Context for its operation.
    */
  def termName(s: String): SimpleName =
    NameCache.cache(SimpleName(s))

  /** Creates a type name for a module class from a string. */
  def moduleClassName(s: String): ObjectClassTypeName =
    termName(s).withObjectSuffix.toTypeName

  sealed abstract class Name derives CanEqual {
    def toDebugString: String = toString
  }

  sealed trait UnsignedName extends Name

  sealed abstract class TermName extends Name

  sealed abstract class UnsignedTermName extends TermName with UnsignedName

  sealed trait SignatureNameItem extends UnsignedTermName:
    def toTypeName: ClassTypeName
  end SignatureNameItem

  final case class SimpleName(name: String) extends UnsignedTermName with SignatureNameItem {
    override def toString: String = name

    lazy val toTypeName: SimpleTypeName = SimpleTypeName(name)(this)

    lazy val withObjectSuffix: ObjectClassName = ObjectClassName(this)

    def prepend(s: String): SimpleName =
      termName(s + name)

    def append(s: String): SimpleName =
      termName(name + s)

    private[tastyquery] def isPackageObjectName: Boolean =
      name == "package" || name.endsWith("$package")
  }

  final case class SignedName(underlying: UnsignedTermName, sig: Signature, target: UnsignedTermName) extends TermName {
    override def toString: String = s"$underlying[with sig $sig @$target]"

    override def toDebugString: String =
      s"${underlying.toDebugString}[with sig ${sig.toDebugString} @${target.toDebugString}]"
  }

  object SignedName:
    def apply(underlying: UnsignedTermName, sig: Signature): SignedName =
      SignedName(underlying, sig, underlying)
  end SignedName

  final case class ExpandedName(prefix: UnsignedTermName, name: SimpleName) extends UnsignedTermName {
    override def toDebugString: String =
      s"${prefix.toDebugString}[Expanded $$$$ $name]"

    override def toString: String = s"$prefix$$$$$name"
  }

  final case class ExpandPrefixName(prefix: UnsignedTermName, name: SimpleName) extends UnsignedTermName {
    override def toDebugString: String =
      s"${prefix.toDebugString}[ExpandPrefix $$ $name]"

    override def toString: String = s"$prefix$$$name"
  }

  final case class SuperAccessorName(underlying: UnsignedTermName) extends UnsignedTermName {
    override def toString: String = s"super$underlying"

    override def toDebugString: String = s"<super:${underlying.toDebugString}>"
  }

  final case class InlineAccessorName(underlying: UnsignedTermName) extends UnsignedTermName {
    override def toString: String = s"inline$underlying"

    override def toDebugString: String = s"<inline:${underlying.toDebugString}>"
  }

  final case class BodyRetainerName(underlying: UnsignedTermName) extends UnsignedTermName {
    override def toString: String = s"<bodyretainer$underlying>" // probably wrong but print something without crashing

    override def toDebugString: String = s"<bodyretainer:$underlying>"
  }

  final case class ObjectClassName private[Names] (underlying: SimpleName)
      extends UnsignedTermName
      with SignatureNameItem {
    override def toString: String = underlying.toString + "$"

    override def toDebugString: String = s"${underlying.toDebugString}[$$]"

    override lazy val toTypeName: ObjectClassTypeName =
      underlying.toTypeName.withObjectSuffix
  }

  final case class UniqueName(underlying: UnsignedTermName, separator: String, num: Int) extends UnsignedTermName {
    override def toString: String = s"$underlying$separator$num"

    override def toDebugString: String = s"${underlying.toDebugString}[unique $separator $num]"
  }

  // can't instantiate directly, might have to nest the other way
  final case class DefaultGetterName(underlying: UnsignedTermName, num: Int) extends UnsignedTermName {
    override def toString: String = s"$underlying$$default$$${num + 1}"

    override def toDebugString: String = s"${underlying.toDebugString}[default $num]"
  }

  sealed abstract class TypeName extends Name with UnsignedName:
    def toTermName: UnsignedTermName
  end TypeName

  sealed trait ClassTypeName extends TypeName:
    def toTermName: SignatureNameItem

    def isObjectClassTypeName: Boolean = this.isInstanceOf[ObjectClassTypeName]

    def companionName: ClassTypeName = this match
      case ObjectClassTypeName(clsName) => clsName
      case name: SimpleTypeName         => name.withObjectSuffix

    def sourceObjectName: SimpleName = this match
      case ObjectClassTypeName(objName) => objName.toTermName
      case name: SimpleTypeName         => name.toTermName

    private[tastyquery] def isPackageObjectClassName: Boolean = this match
      case ObjectClassTypeName(objName) => objName.toTermName.isPackageObjectName
      case _                            => false
  end ClassTypeName

  final case class SimpleTypeName private[Names] (name: String)(val toTermName: SimpleName)
      extends TypeName
      with ClassTypeName:
    override def toString(): String = name

    override def toDebugString: String = s"$name/T"

    lazy val withObjectSuffix: ObjectClassTypeName = ObjectClassTypeName(this)
  end SimpleTypeName

  final case class ObjectClassTypeName private[Names] (underlying: SimpleTypeName) extends TypeName with ClassTypeName:
    override def toString(): String = s"$underlying$$"

    override def toDebugString: String = s"${underlying.toDebugString}[$$]"

    override lazy val toTermName: ObjectClassName =
      underlying.toTermName.withObjectSuffix
  end ObjectClassTypeName

  final case class UniqueTypeName(base: TypeName, separator: String, num: Int) extends TypeName:
    override def toString(): String = s"$base$separator$num"

    override def toDebugString: String = s"${base.toDebugString}[unique $separator $num]"

    def toTermName: UniqueName = UniqueName(base.toTermName, separator, num)
  end UniqueTypeName

  final case class PackageFullName(path: List[SimpleName]):
    override def toString(): String =
      path.mkString(".")

    // for consistency with other name types, but it is always the same as toString() here
    def toDebugString: String =
      toString()

    def select(subPackage: SimpleName): PackageFullName =
      PackageFullName(path :+ subPackage)

    private[tastyquery] def simpleName: SimpleName = path match
      case Nil  => nme.UserLandRootPackageName
      case path => path.last
  end PackageFullName

  object PackageFullName:
    val rootPackageName = PackageFullName(Nil)
    val emptyPackageName = PackageFullName(nme.EmptyPackageName :: Nil)
    val scalaPackageName = PackageFullName(nme.scalaPackageName :: Nil)
    val javaLangPackageName = PackageFullName(nme.javaPackageName :: nme.langPackageName :: Nil)

    private[tastyquery] val scalaRuntimePackageName =
      PackageFullName(nme.scalaPackageName :: termName("runtime") :: Nil)

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
