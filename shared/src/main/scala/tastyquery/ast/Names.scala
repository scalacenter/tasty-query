package tastyquery.ast

import tastyquery.unsafe
import tastyquery.util.syntax.chaining.given

import java.util.concurrent.ConcurrentHashMap

import dotty.tools.tasty.TastyFormat.NameTags

import scala.reflect.NameTransformer

import scala.io.Codec
import scala.annotation.targetName

import scala.jdk.CollectionConverters.*

import Names.SimpleName

private[ast] object NameCache {

  // A map from the name to itself. Used to keep only one instance of SimpleName by underlying String
  private val nameTable: scala.collection.concurrent.Map[SimpleName, SimpleName] =
    new ConcurrentHashMap[SimpleName, SimpleName]().asScala

  private[ast] def cache(newName: SimpleName): SimpleName = {
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
    val RefinementClass = typeName("<refinement>")

    val scalaPackageName: TermName = termName("scala")
    val javaPackageName: TermName = termName("java")
    val javalangPackageName: TermName = javaPackageName.select(termName("lang"))
  }

  object tpnme {
    val Any: TypeName = typeName("Any")
    val Nothing: TypeName = typeName("Nothing")
    val Null: TypeName = typeName("Null")

    val Array: TypeName = typeName("Array")

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

    val scalaFunction0: TypeName = nme.scalaPackageName.select(termName("Function0")).toTypeName
  }

  /** Create a type name from the characters in cs[offset..offset+len-1].
    * Assume they are already encoded.
    */
  def typeName(cs: Array[Char], offset: Int, len: Int): TypeName =
    termName(cs, offset, len).toTypeName

  /** Create a type name from the UTF8 encoded bytes in bs[offset..offset+len-1].
    * Assume they are already encoded.
    */
  def typeName(bs: Array[Byte], offset: Int, len: Int): TypeName =
    termName(bs, offset, len).toTypeName

  @targetName("typeNameFromImmutableBytes")
  def typeName(bs: IArray[Byte], offset: Int, len: Int): TypeName =
    termName(bs, offset, len).toTypeName

  /** Create a type name from a string */
  def typeName(s: String): TypeName =
    termName(s).toTypeName

  /** Create a term name from a string.
    * See `sliceToTermName` in `Decorators` for a more efficient version
    * which however requires a Context for its operation.
    */
  def termName(s: String): SimpleName =
    NameCache.cache(SimpleName(s))

  /** Create a term name from the characters in cs[offset..offset+len-1].
    * Assume they are already encoded.
    */
  def termName(cs: Array[Char], offset: Int, len: Int): SimpleName =
    NameCache.cache(SimpleName(cs.slice(offset, offset + len).mkString))

  /** Create a term name from the UTF8 encoded bytes in bs[offset..offset+len-1].
    * Assume they are already encoded.
    */
  def termName(bs: Array[Byte], offset: Int, len: Int): SimpleName = {
    val chars = Codec.fromUTF8(bs, offset, len)
    termName(chars, 0, chars.length)
  }

  @targetName("termNameFromImmutableBytes")
  def termName(bs: IArray[Byte], offset: Int, len: Int): SimpleName =
    termName(unsafe.asByteArray(bs), offset, len)

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

    private var myTypeName: TypeName | Null = null

    override def toTypeName: TypeName = {
      val local1 = myTypeName
      if local1 == null then {
        synchronized {
          val local2 = myTypeName
          if local2 == null then TypeName(this).useWith { myTypeName = _ }
          else local2
        }
      } else {
        local1
      }
    }

    infix def select(name: SimpleName): QualifiedName = QualifiedName(NameTags.QUALIFIED, this, name)

    def subnames: TermName.SubNamesOps = new TermName.SubNamesOps(this)

    def withObjectSuffix: SuffixedName = SuffixedName(NameTags.OBJECTCLASS, this)
    def stripObjectSuffix: TermName = this match
      case SuffixedName(NameTags.OBJECTCLASS, rest) => rest
      case _                                        => this
  }

  object TermName {
    class SubNamesOps(val termName: TermName) extends AnyVal {
      def foreach(f: TermName => Unit): Unit = {
        def addStack(name: TermName): Unit = name match
          case name @ QualifiedName(NameTags.QUALIFIED, pre, _) => { addStack(pre); f(name) }
          case name @ SimpleName(_)                             => f(name)
          case _                                                => ()
        addStack(termName)
      }
    }
  }

  final case class SimpleName(name: String) extends TermName {
    override def tag: Int = NameTags.UTF8

    override def asSimpleName: SimpleName = this

    override def isEmpty: Boolean = name.length == 0

    override def toString: String = name

    def append(s: String): SimpleName =
      termName(s"$name$s")
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
  }

  final case class QualifiedName(override val tag: Int, prefix: TermName, name: SimpleName)
      extends DerivedName(prefix) {
    def separator: String = tag match {
      case NameTags.QUALIFIED    => "."
      case NameTags.EXPANDED     => "$$"
      case NameTags.EXPANDPREFIX => "$"
    }

    override def toDebugString: String =
      s"${prefix.toDebugString}[Qualified $separator $name]"

    override def toString: String = s"$prefix$separator$name"
  }

  final case class PrefixedName(override val tag: Int, override val underlying: TermName)
      extends DerivedName(underlying) {
    override def toString: String = tag match {
      case NameTags.SUPERACCESSOR  => s"super$underlying"
      case NameTags.INLINEACCESSOR => s"inline$underlying"
    }
  }

  final case class SuffixedName(override val tag: Int, override val underlying: TermName)
      extends DerivedName(underlying) {
    override def toString: String = tag match {
      case NameTags.BODYRETAINER => ???
      case NameTags.OBJECTCLASS  => underlying.toString
    }

    override def toDebugString: String = tag match {
      case NameTags.BODYRETAINER => ???
      case NameTags.OBJECTCLASS  => s"${underlying.toDebugString}[$$]"
    }
  }

  abstract class NumberedName(underlying: TermName, num: Int) extends DerivedName(underlying)

  // TODO: factor out the separators
  final case class UniqueName(separator: String, override val underlying: TermName, num: Int)
      extends NumberedName(underlying, num) {
    override def tag: Int = NameTags.UNIQUE

    override def toString: String = s"$underlying$separator$num"
  }

  // can't instantiate directly, might have to nest the other way
  final case class DefaultGetterName(override val underlying: TermName, num: Int)
      extends NumberedName(underlying, num) {
    override def tag: Int = NameTags.DEFAULTGETTER

    override def toString: String = s"$underlying$$default$num"
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
  }
}
