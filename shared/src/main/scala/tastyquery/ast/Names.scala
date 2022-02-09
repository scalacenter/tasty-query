package tastyquery.ast

import tastyquery.unsafe
import tastyquery.util.syntax.chaining.given

import java.util.concurrent.ConcurrentHashMap

import dotty.tools.tasty.TastyFormat.NameTags

import scala.io.Codec
import scala.annotation.targetName

object Names {

  given Ordering[SimpleName] = Ordering.by(_.name)

  object str {
    val topLevelSuffix = "$package"
  }

  object attr {
    val TASTY = termName("TASTY")
    val Scala = termName("Scala")
    val ScalaSig = termName("ScalaSig")
    val RuntimeVisibleAnnotations = termName("RuntimeVisibleAnnotations") // RetentionPolicy.RUNTIME
    val RuntimeInvisibleAnnotations = termName("RuntimeInvisibleAnnotations") // RetentionPolicy.CLASS
  }

  object annot {
    val ScalaSignature = termName("Lscala/reflect/ScalaSignature;")
    val ScalaLongSignature = termName("Lscala/reflect/ScalaLongSignature;")
  }

  import scala.jdk.CollectionConverters._

  // A map from the name to itself. Used to keep only one instance of SimpleName by underlying String
  private val nameTable: scala.collection.concurrent.Map[SimpleName, SimpleName] =
    new ConcurrentHashMap[SimpleName, SimpleName]().asScala

  /** The term name represented by the empty string */
  val EmptySimpleName: SimpleName = termName("")
  val EmptyTermName: SimpleName = EmptySimpleName
  val EmptyTypeName: TypeName = EmptyTermName.toTypeName
  val RootName: SimpleName = termName("<root>")
  val EmptyPackageName: SimpleName = termName("<empty>")
  val Constructor: SimpleName = termName("<init>")
  val Wildcard: SimpleName = termName("_")
  val RefinementClass = typeName("<refinement>")

  val SuperAccessorPrefix: String = "super$"
  val InlineAccessorPrefix: String = "inline$"
  val BodyRetainerSuffix: String = "$retainedBody"

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
    cache(SimpleName(s))

  /** Create a term name from the characters in cs[offset..offset+len-1].
    * Assume they are already encoded.
    */
  def termName(cs: Array[Char], offset: Int, len: Int): SimpleName =
    cache(SimpleName(cs.slice(offset, offset + len).mkString))

  private def cache(newName: SimpleName): SimpleName = {
    val oldName = nameTable.putIfAbsent(newName, newName)
    oldName.getOrElse(newName)
  }

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
      case NameTags.OBJECTCLASS  => s"$underlying$$"
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

    override def toDebugString: String = s"$toString/T"

    def toObjectName: TypeName = SuffixedName(NameTags.OBJECTCLASS, toTermName).toTypeName
  }
}
