package simple_trees

/** Doc of class Docstrings.
  *
  * @param ctorParam doc of ctorParam
  */
class Docstrings[/** Doc of T. */ T](/** Doc of ctorParam. */ val ctorParam: Int):
  /** Doc of secondary constructor. */
  def this() = this(0)

  /** Doc of method. */
  def method(/** Doc of param. */ param: Int): Int = param

  /** Doc of value. */
  val value: Int = 1

  /** Doc of variable. */
  var variable: Int = 2

  /** Doc of lazy value. */
  lazy val lazyValue: Int = 3

  /** Doc of type member. */
  type TypeMember = Int

  /** Doc of abstract type member. */
  type AbstractTypeMember

  /** Doc of nested class. */
  class NestedClass

  /** Doc of nested object. */
  object NestedObject

  /** Doc of given. */
  given Ordering[Docstrings[?]] = Ordering.by(_.ctorParam)

  def undocumented: Int = 4

  /** Doc with non-ASCII: café — ünïcödé ✓ 日本語 */
  def nonAscii: Int = 7

  /** Doc of local. */
  def withLocal: Int =
    /** Doc of local value. */
    val local = 5
    local
end Docstrings

/** Doc of object Docstrings. */
object Docstrings:
  /** Doc of object member. */
  def objectMember: Int = 6

/** Doc of trait. */
trait DocstringsTrait

/** Doc of enum. */
enum DocstringsEnum:
  /** Doc of enum case. */
  case Case1

  /** Doc of parameterized enum case. */
  case Case2(x: Int)

/** Doc of standalone object. */
object DocstringsStandaloneObject

/** Doc of case class. */
case class DocstringsCaseClass(/** Doc of case class param. */ x: Int)
