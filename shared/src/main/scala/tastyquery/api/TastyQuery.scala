package tastyquery.api

import tastyquery.Contexts.ContextBase
import tastyquery.ast.Trees.Tree

class TastyTrees(trees: List[Tree])

class TastyQuery private[api] (ctx: ContextBase, trees: TastyTrees) {}
