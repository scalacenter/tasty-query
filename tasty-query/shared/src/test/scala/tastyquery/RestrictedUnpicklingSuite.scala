package tastyquery

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future

import tastyquery.Contexts.Context
import tastyquery.Trees.Tree

import Paths.*

abstract class RestrictedUnpicklingSuite extends BaseUnpicklingSuite {
  def getUnpicklingContext(path: TopLevelDeclPath, extraClasspath: TopLevelDeclPath*): Future[Context] =
    initRestrictedContext(path, extraClasspath)

  protected def findTopLevelTasty(path: TopLevelDeclPath)(extras: TopLevelDeclPath*): Future[(Context, Tree)] =
    for base <- initRestrictedContext(path, extras) yield
      val topLevelClass = path.rootClassName
      val rootSym = base.findSymbolFromRoot(path.toNameList)
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
