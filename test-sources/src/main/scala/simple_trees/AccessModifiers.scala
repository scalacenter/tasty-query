package simple_trees

import scala.annotation.nowarn

@nowarn("msg=Ignoring \\[this\\] qualifier")
class AccessModifiers(
  localParam: Int,
  private[this] val privateThisParam: Int,
  private val privateParam: Int,
  private val accessedPrivateParam: Int,
  private[simple_trees] val scopedPrivateParam: Int,
  protected[this] val protectedThisParam: Int,
  protected val protectedParam: Int,
  protected val accessedProtectedParam: Int,
  protected[simple_trees] val scopedProtectedParam: Int,
  val publicParam: Int
):
  private[this] val privateThisField: Int = 1
  private val privateField: Int = 1
  private val accessedPrivateField: Int = 1
  private[simple_trees] val scopedPrivateField: Int = 1
  protected[this] val protectedThisField: Int = 1
  protected val protectedField: Int = 1
  protected val accessedProtectedField: Int = 1
  protected[simple_trees] val scopedProtectedField: Int = 1
  val publicField: Int = 1
end AccessModifiers

object AccessModifiers:
  def access(x: AccessModifiers): Int =
    x.accessedPrivateParam + x.accessedProtectedParam + x.accessedPrivateField + x.accessedProtectedField
end AccessModifiers
