package tastyquery

import tastyquery.Contexts.Context
import tastyquery.ast.Symbols.ClassSymbol
import tastyquery.ast.Types.SymResolutionProblem

import Paths.*

abstract class RestrictedUnpicklingSuite extends BaseUnpicklingSuite {
  import RestrictedUnpicklingSuite.*

  def getUnpicklingContext(path: TopLevelDeclPath, extraClasspath: TopLevelDeclPath*): Context =
    initRestrictedContext(path, extraClasspath)

  protected def findTopLevelClass(path: TopLevelDeclPath)(extras: TopLevelDeclPath*): (Context, ClassSymbol) = {
    val base = initRestrictedContext(path, extras)
    val topLevelClass = path.rootClassName
    val classRoot = base.getClassIfDefined(topLevelClass) match
      case Right(cls) => cls
      case Left(err)  => throw MissingTopLevelDecl(path, err)
    if !base.classloader.scanClass(classRoot)(using base) then fail(s"could not initialise $topLevelClass, $classRoot")
    (base, classRoot)
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
