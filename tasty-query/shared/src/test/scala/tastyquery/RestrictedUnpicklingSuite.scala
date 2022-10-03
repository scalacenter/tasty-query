package tastyquery

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future

import tastyquery.Contexts.Context
import tastyquery.Trees.Tree
import tastyquery.Types.SymResolutionProblem

import Paths.*

abstract class RestrictedUnpicklingSuite extends BaseUnpicklingSuite {
  import RestrictedUnpicklingSuite.*

  def getUnpicklingContext(path: TopLevelDeclPath, extraClasspath: TopLevelDeclPath*): Future[Context] =
    initRestrictedContext(path, extraClasspath)

  protected def findTopLevelTasty(path: TopLevelDeclPath)(extras: TopLevelDeclPath*): Future[(Context, Tree)] =
    for base <- initRestrictedContext(path, extras) yield
      val topLevelClass = path.rootClassName
      val rootSym = base.rootSymbolsIfDefined(topLevelClass) match
        case rootSym :: _ => rootSym
        case _            => fail(s"Missing class for $topLevelClass")
      val tree = base.classloader.topLevelTasty(rootSym)(using base) match
        case Some(trees) => trees.head
        case _           => fail(s"Missing tasty for $topLevelClass, but resolved root $rootSym")
      (base, tree)
  end findTopLevelTasty

  private def initRestrictedContext(path: TopLevelDeclPath, extras: Seq[TopLevelDeclPath]): Future[Context] =
    for classpath <- testClasspath yield
      val filtered = classpath.withFilter((path :: extras.toList).map(_.rootClassName))
      Contexts.init(filtered)
}

object RestrictedUnpicklingSuite {
  class MissingTopLevelDecl(path: TopLevelDeclPath, cause: SymResolutionProblem)
      extends Exception(
        s"Missing top-level declaration ${path.rootClassName}, perhaps it is not on the classpath?",
        cause
      )
}
