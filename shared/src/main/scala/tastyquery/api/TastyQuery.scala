package tastyquery.api

import tastyquery.Contexts.Context
import tastyquery.ast.Symbols.{Symbol, DeclaringSymbol}
import tastyquery.ast.Trees.{Tree, DefTree}

class TastyTrees(trees: List[Tree]):

  private[tastyquery] def debugDefinitions: Unit =
    for tree <- trees do
      tree.walkTree {
        case ddef: DefTree =>
          def nameOf(s: Symbol): String =
            if s.owner.nn.isStatic then s.fullName.toDebugString
            else s"${nameOf(s.owner.nn)} { ${s.name.toDebugString} }"
          if ddef.symbol.exists then println(nameOf(ddef.symbol))
        case _ =>
      }

class TastyQuery private[api] (ctx: Context, trees: TastyTrees):
  export trees.debugDefinitions
