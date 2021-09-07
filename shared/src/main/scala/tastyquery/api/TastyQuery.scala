package tastyquery.api

import tastyquery.Contexts.BaseContext
import tastyquery.ast.Trees.Tree

class TastyTrees(trees: List[Tree])

class TastyQuery private[api] (ctx: BaseContext, trees: TastyTrees) {}
