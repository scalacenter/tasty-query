package tastyquery

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Traversers.*
import tastyquery.Trees.*

object TestUtils:
  extension (sc: StringContext)
    def name(): SimpleName =
      termName(sc.parts.mkString)
    def tname(): SimpleTypeName =
      typeName(sc.parts.mkString)

  def findLocalValDef(body: Tree, name: TermName): TermSymbol =
    findTree(body) {
      case vd: ValDef if vd.name == name => vd.symbol
    }
  end findLocalValDef

  def findTree[A](body: Tree)(test: PartialFunction[Tree, A]): A =
    object finder extends TreeTraverser:
      var result: Option[A] = None

      override def traverse(tree: Tree): Unit =
        if result.isEmpty then
          tree match
            case test(res) => result = Some(res)
            case _         => super.traverse(tree)
      end traverse
    end finder

    finder.traverse(body)
    finder.result.getOrElse {
      throw new AssertionError(s"Could not find the right tree in body\n$body")
    }
  end findTree
end TestUtils
