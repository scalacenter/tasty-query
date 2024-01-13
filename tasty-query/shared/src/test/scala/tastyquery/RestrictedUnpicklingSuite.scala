package tastyquery

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future

import tastyquery.Classpaths.*
import tastyquery.Contexts.*
import tastyquery.Symbols.*
import tastyquery.Trees.*

abstract class RestrictedUnpicklingSuite extends BaseUnpicklingSuite {
  def getUnpicklingContext(rootSymbolPath: String, extraRootSymbolPaths: String*): Future[Context] =
    initRestrictedContext(rootSymbolPath, extraRootSymbolPaths)

  protected def findTopLevelTasty(rootSymbolPath: String)(extraRootSymbolPaths: String*): Future[(Context, Tree)] =
    for base <- initRestrictedContext(rootSymbolPath, extraRootSymbolPaths) yield
      given Context = base
      val rootSym = findTopLevelClassOrModuleClass(rootSymbolPath)
      val tree = rootSym.topLevelTasty match
        case firstTree :: _ => firstTree
        case Nil            => fail(s"Missing tasty for $rootSymbolPath, but resolved root $rootSym")
      (base, tree)
  end findTopLevelTasty

  protected def findTopLevelClassOrModuleClass(rootSymbolPath: String)(using Context): ClassSymbol =
    if rootSymbolPath.endsWith("$") then ctx.findTopLevelModuleClass(rootSymbolPath.stripSuffix("$"))
    else ctx.findTopLevelClass(rootSymbolPath)

  private def initRestrictedContext(rootSymbolPath: String, extraRootSymbolPaths: Seq[String]): Future[Context] =
    for classpath <- testClasspath yield
      val allowedBinaryNames = (rootSymbolPath :: extraRootSymbolPaths.toList).map(_.stripSuffix("$"))
      val filtered = classpath.map(FilteredClasspathEntry(_, allowedBinaryNames))
      Context.initialize(filtered)

  private class FilteredClasspathEntry(base: ClasspathEntry, allowedBinaryNames: List[String]) extends ClasspathEntry:
    private def packageAndClass(binaryName: String): (String, String) =
      val lastSep = binaryName.lastIndexOf('.')
      if lastSep == -1 then ("", binaryName)
      else
        import scala.language.unsafeNulls
        val packageName = binaryName.substring(0, lastSep)
        val className = binaryName.substring(lastSep + 1)
        (packageName, className)

    private val lookup = allowedBinaryNames.map(packageAndClass).groupMap((pkg, _) => pkg)((_, cls) => cls)

    override def toString(): String = base.toString()

    def listAllPackages(): List[PackageData] =
      for
        pkg <- base.listAllPackages()
        allowedClassBinaryNames <- lookup.get(pkg.dotSeparatedName)
      yield FilteredPackageData(pkg, allowedClassBinaryNames)
  end FilteredClasspathEntry

  private class FilteredPackageData(base: PackageData, allowedClassBinaryNames: List[String]) extends PackageData:
    val dotSeparatedName = base.dotSeparatedName

    override def toString(): String = base.toString()

    def listAllClassDatas(): List[ClassData] =
      base.listAllClassDatas().filter(c => allowedClassBinaryNames.contains(c.binaryName))

    def getClassDataByBinaryName(binaryName: String): Option[ClassData] =
      if allowedClassBinaryNames.contains(binaryName) then base.getClassDataByBinaryName(binaryName)
      else None
  end FilteredPackageData
}
