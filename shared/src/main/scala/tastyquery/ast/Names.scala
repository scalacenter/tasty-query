package tastyquery.ast

import java.util.concurrent.ConcurrentHashMap

import dotty.tools.tasty.TastyFormat.NameTags

import scala.io.Codec

object Names {

  /** The term name represented by the empty string */
  val EmptyTermName: SimpleName = SimpleName("")
  val RootName: SimpleName      = SimpleName("<root>")
  val Wildcard: SimpleName      = SimpleName("_")

  val SuperAccessorPrefix: String  = "super$"
  val InlineAccessorPrefix: String = "inline$"
  val BodyRetainerSuffix: String   = "$retainedBody"

  import scala.jdk.CollectionConverters._

  // A map from the name to itself. Used to keep only one instance of SimpleName by underlying String
  private val nameTable: scala.collection.concurrent.Map[SimpleName, SimpleName] =
    new ConcurrentHashMap[SimpleName, SimpleName]().asScala

  /**
   * Create a type name from the characters in cs[offset..offset+len-1].
   * Assume they are already encoded.
   */
  def typeName(cs: Array[Char], offset: Int, len: Int): TypeName =
    termName(cs, offset, len).toTypeName

  /**
   * Create a type name from the UTF8 encoded bytes in bs[offset..offset+len-1].
   * Assume they are already encoded.
   */
  def typeName(bs: Array[Byte], offset: Int, len: Int): TypeName =
    termName(bs, offset, len).toTypeName

  /** Create a type name from a string */
  def typeName(s: String): TypeName = typeName(s.toCharArray, 0, s.length)

  /**
   * Create a term name from a string.
   * See `sliceToTermName` in `Decorators` for a more efficient version
   * which however requires a Context for its operation.
   */
  def termName(s: String): SimpleName = termName(s.toCharArray, 0, s.length)

  /**
   * Create a term name from the characters in cs[offset..offset+len-1].
   * Assume they are already encoded.
   */
  def termName(cs: Array[Char], offset: Int, len: Int): SimpleName = {
    val newName = SimpleName(cs.slice(offset, offset + len).mkString)
    val oldName = nameTable.putIfAbsent(newName, newName)
    oldName.getOrElse(newName)
  }

  /**
   * Create a term name from the UTF8 encoded bytes in bs[offset..offset+len-1].
   * Assume they are already encoded.
   */
  def termName(bs: Array[Byte], offset: Int, len: Int): SimpleName = {
    val chars = Codec.fromUTF8(bs, offset, len)
    termName(chars, 0, chars.length)
  }

  abstract class Name extends Designator {

    /** This name converted to a type name */
    def toTypeName: TypeName

    /** This name downcasted to a simple term name */
    def asSimpleName: SimpleName

    def isEmpty: Boolean

    override def hashCode: Int = System.identityHashCode(this)
  }

  abstract class TermName extends Name {
    def tag: Int

    private var myTypeName: TypeName = null

    override def toTypeName: TypeName = {
      if (myTypeName == null) {
        synchronized {
          if (myTypeName == null) myTypeName = new TypeName(this)
        }
      }
      myTypeName
    }
  }

  final case class SimpleName(name: String) extends TermName {
    override def tag: Int = NameTags.UTF8

    override def asSimpleName: SimpleName = this

    override def isEmpty: Boolean = name.length == 0

    override def hashCode: Int = name.hashCode

    override def toString: String = name
  }

  abstract class DerivedName(val underlying: TermName) extends TermName {
    override def asSimpleName: SimpleName = throw new UnsupportedOperationException(
      s"$this is not a simple " +
        s"name"
    )

    override def isEmpty: Boolean = false
  }

  final case class SignedName(override val underlying: TermName, sig: Signature) extends DerivedName(underlying) {
    override def tag: Int = NameTags.SIGNED

    override def toString: String = s"$underlying[with sig ${sig}]"
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

  final case class TypeName(val toTermName: TermName) extends Name {
    override def toTypeName: TypeName = this

    override def asSimpleName: SimpleName = toTermName.asSimpleName

    override def isEmpty: Boolean = toTermName.isEmpty

    override def toString: String = toTermName.toString
  }
}
