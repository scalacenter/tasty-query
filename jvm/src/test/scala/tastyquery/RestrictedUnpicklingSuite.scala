package tastyquery

import tastyquery.Contexts.BaseContext
import tastyquery.ast.Symbols.{ClassSymbol, Symbol}
import tastyquery.ast.Trees.Tree
import tastyquery.ast.Types.{Type, SymResolutionProblem}

import BaseUnpicklingSuite.Decls.*

abstract class RestrictedUnpicklingSuite extends BaseUnpicklingSuite {
  import RestrictedUnpicklingSuite.*

  def getUnpicklingContext(path: TopLevelDeclPath, extraClasspath: TopLevelDeclPath*): BaseContext =
    initRestrictedContext(path, extraClasspath)

  protected def findTopLevelClass(path: TopLevelDeclPath)(extras: TopLevelDeclPath*): (BaseContext, ClassSymbol) = {
    val base = initRestrictedContext(path, extras)
    val topLevelClass = path.fullClassName
    val classRoot = base.getClassIfDefined(topLevelClass) match
      case Right(cls) => cls
      case Left(err)  => throw MissingTopLevelDecl(path, err)
    if !base.classloader.scanClass(classRoot)(using base) then fail(s"could not initialise $topLevelClass, $classRoot")
    (base, classRoot)
  }

  private def initRestrictedContext(path: TopLevelDeclPath, extras: Seq[TopLevelDeclPath]): BaseContext =
    val classpath = testClasspath.withFilter((path :: extras.toList).map(_.fullClassName))
    Contexts.init(classpath)
}

object RestrictedUnpicklingSuite {
  class MissingTopLevelDecl(path: TopLevelDeclPath, cause: SymResolutionProblem)
      extends Exception(
        s"Missing top-level declaration ${path.fullClassName}, perhaps it is not on the classpath?",
        cause
      )
}
