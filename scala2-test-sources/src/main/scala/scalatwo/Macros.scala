package scalatwo

import scala.language.experimental.macros

import scala.reflect.macros.blackbox.Context

object Macros {
  def foo[X](x: X): Any = macro fooImpl[X]

  def fooImpl[X](c: Context)(x: c.Expr[X]): c.Expr[Any] = ???
}
