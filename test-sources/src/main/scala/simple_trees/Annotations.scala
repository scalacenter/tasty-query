package simple_trees

import scala.annotation.implicitNotFound

import javadefined.JavaAnnotWithDefault

class Annotations:
  @inline
  def inlineMethod(): Unit = ()

  @inline
  @deprecated("some reason", since = "1.0")
  def inlineDeprecatedMethod(): Unit = ()

  @deprecated(since = "forever", message = "reason")
  val deprecatedVal: Int = 5

  @implicitNotFound("Cannot find implicit for MyTypeClass[${T}]")
  trait MyTypeClass[T]

  @deprecated("other reason", "forever")
  type IntAlias = Int

  @JavaAnnotWithDefault
  def javaAnnotWithDefaultImplicit(): Int = 0

  @JavaAnnotWithDefault(false)
  def javaAnnotWithDefaultExplicit(): Int = 1
end Annotations
