package tastyquery

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*

object TestUtils:
  def findLocalValDef(body: Tree, name: TermName)(using Context): TermSymbol =
    findTree(body) {
      case vd: ValDef if vd.name == name => vd.symbol
    }
  end findLocalValDef

  def findTree[A](body: Tree)(test: PartialFunction[Tree, A])(using Context): A =
    var result: Option[A] = None
    body.walkTree { tree =>
      tree match
        case test(res) => result = Some(res)
        case _         => ()
    }
    result.getOrElse {
      throw new AssertionError(s"Could not find the right tree in body\n$body")
    }
  end findTree
end TestUtils
