package simple_trees

import scala.quoted.*

object QuotesAndSplices:
  def termQuote(using Quotes): Expr[String] =
    '{ "hello" }

  def termSplice(using Quotes)(s: Expr[String]): Expr[String] =
    '{ $s + "foo" }

  /* Reading only -- mostly making sure that there isn't a separate TYPESPLICE
   * tag that we don't know about.
   */
  def typeSplice[T: Type](using Quotes)(e: Expr[T]): Expr[T] =
    '{ $e: T }

  def termQuotePattern(using quotes: Quotes)(e: Expr[Int]): Expr[Int] =
    e match
      case '{ ($a: Int) + 1 } => a

  def typeQuotePattern(using quotes: Quotes): Expr[Unit] =
    Type.of[Any] match
      case '[Map[t, u]] => '{ () }
end QuotesAndSplices
