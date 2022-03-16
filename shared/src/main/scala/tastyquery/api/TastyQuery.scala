package tastyquery.api

import tastyquery.Contexts.BaseContext
import tastyquery.ast.Symbols.{Symbol, DeclaringSymbol}
import tastyquery.ast.Trees.{Tree, DefTree}

class TastyTrees(trees: List[Tree]):

  private[tastyquery] def debugDefinitions: Unit =
    for tree <- trees do
      tree.walkTree {
        case ddef: DefTree =>
          def nameOf(s: Symbol): String =
            if s.outer.isStatic then s.fullName.toDebugString
            else s"${nameOf(s.outer)} { ${s.name.toDebugString} }"
          if ddef.symbol.exists then println(nameOf(ddef.symbol))
        case _ =>
      }

class TastyQuery private[api] (ctx: BaseContext, trees: TastyTrees):
  export trees.debugDefinitions
