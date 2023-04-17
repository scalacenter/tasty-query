package simple_trees

import scala.quoted.*

object QuotesAndSplices:
  def typeQuoteMatching(using quotes: Quotes): Expr[Unit] =
    Type.of[Any] match
      case '[Map[t, u]] => '{ () }
end QuotesAndSplices
