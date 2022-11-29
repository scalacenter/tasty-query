package tastyquery

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future

import tastyquery.Contexts.*
import tastyquery.Symbols.*
import tastyquery.Trees.*

import Paths.*

abstract class RestrictedUnpicklingSuite extends BaseUnpicklingSuite {
  def getUnpicklingContext(rootSymbolPath: String, extraRootSymbolPaths: String*): Future[Context] =
    initRestrictedContext(rootSymbolPath, extraRootSymbolPaths)

  protected def findTopLevelTasty(rootSymbolPath: String)(extraRootSymbolPaths: String*): Future[(Context, Tree)] =
    for base <- initRestrictedContext(rootSymbolPath, extraRootSymbolPaths) yield
      given Context = base
      val rootSym = findTopLevelClassOrModuleClass(rootSymbolPath)
      val tree = base.classloader.topLevelTasty(rootSym) match
        case Some(trees) => trees.head
        case _           => fail(s"Missing tasty for $rootSymbolPath, but resolved root $rootSym")
      (base, tree)
  end findTopLevelTasty

  protected def findTopLevelClassOrModuleClass(rootSymbolPath: String)(using Context): ClassSymbol =
    if rootSymbolPath.endsWith("$") then ctx.findTopLevelModuleClass(rootSymbolPath.stripSuffix("$"))
    else ctx.findTopLevelClass(rootSymbolPath)

  private def initRestrictedContext(rootSymbolPath: String, extraRootSymbolPaths: Seq[String]): Future[Context] =
    for classpath <- testClasspath yield
      val filtered = classpath.withFilter((rootSymbolPath :: extraRootSymbolPaths.toList).map(_.stripSuffix("$")))
      Contexts.init(filtered)
}
