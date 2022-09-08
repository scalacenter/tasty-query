package tastyquery

import tastyquery.Contexts.Context
import tastyquery.ast.Trees.Tree
import tastyquery.ast.Types.SymResolutionProblem

import Paths.*

abstract class RestrictedUnpicklingSuite extends BaseUnpicklingSuite {
  import RestrictedUnpicklingSuite.*

  def getUnpicklingContext(path: TopLevelDeclPath, extraClasspath: TopLevelDeclPath*): Context =
    initRestrictedContext(path, extraClasspath)

  protected def findTopLevelTasty(path: TopLevelDeclPath)(extras: TopLevelDeclPath*): (Context, Tree) = {
    val base = initRestrictedContext(path, extras)
    val topLevelClass = path.rootClassName
    val rootSym = base.rootSymbolsIfDefined(topLevelClass) match
      case rootSym :: _ => rootSym
      case _            => fail(s"Missing class for $topLevelClass")
    val tree = base.classloader.topLevelTasty(rootSym)(using base) match
      case Some(trees) => trees.head
      case _           => fail(s"Missing tasty for $topLevelClass, but resolved root $rootSym")
    (base, tree)
  }

  private def initRestrictedContext(path: TopLevelDeclPath, extras: Seq[TopLevelDeclPath]): Context =
    val classpath = testClasspath.withFilter((path :: extras.toList).map(_.rootClassName))
    Contexts.init(classpath)
}

object RestrictedUnpicklingSuite {
  class MissingTopLevelDecl(path: TopLevelDeclPath, cause: SymResolutionProblem)
      extends Exception(
        s"Missing top-level declaration ${path.rootClassName}, perhaps it is not on the classpath?",
        cause
      )
}
