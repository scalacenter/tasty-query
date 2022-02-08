package tastyquery.reader.classfiles

import tastyquery.ast.Names.SimpleName
import scala.reflect.NameTransformer
import tastyquery.Contexts.{BaseContext, baseCtx, defn}
import scala.collection.mutable
import tastyquery.ast.Names.{TermName, EmptyPackageName, termName, str}
import tastyquery.ast.Symbols.PackageClassSymbol
import tastyquery.ast.Symbols.ClassSymbol
import tastyquery.ast.Symbols.DeclaringSymbol

object Classpaths {

  /** Contains class data and tasty data. `name` is a Scala identifier */
  case class PackageData(name: SimpleName, classes: IArray[ClassData], tastys: IArray[TastyData])

  /** Contains class bytes. `simpleName` is a Scala identifier */
  case class ClassData(simpleName: SimpleName, debugPath: String, bytes: IArray[Byte])

  /** Contains tasty bytes. `simpleName` is a Scala identifier */
  case class TastyData(simpleName: SimpleName, debugPath: String, bytes: IArray[Byte])

  def enterRoot(root: ClassData, owner: DeclaringSymbol)(using BaseContext): ClassSymbol = {
    val clsName = root.simpleName.toTypeName
    val objclassName = clsName.toObjectName
    val objName = root.simpleName

    locally {
      baseCtx.createSymbolIfNew(objName, owner)
      baseCtx.createClassSymbolIfNew(objclassName, owner)
    }
    baseCtx.createClassSymbolIfNew(clsName, owner)
  }

  sealed abstract class Classpath protected (val packages: IArray[PackageData]) {
    def loader: Loader = Loader(this)
  }

  object Classpath {
    case object Empty extends Classpath(IArray.empty)

    def from(packages: IArray[PackageData]): Classpath =
      if (packages.isEmpty) Empty
      else new Classpath(packages) {}
  }

  class Loader(val classpath: Classpath) { loader =>

    private var searched = false
    private var index: Map[PackageClassSymbol, IArray[ClassData]] = Map.empty
    private var uninitialised: Map[ClassSymbol, ClassData] = Map.empty

    /** sentinel value, it proves that `baseCtx.withRoot` can only be called from `scanClass` */
    opaque type LoadRoot = Null
    protected final given loadRoot: LoadRoot = null

    def lookupTasty(fullClassName: String): Option[TastyData] =
      def packageAndClass(fullClassName: String): (SimpleName, SimpleName) = {
        val lastSep = fullClassName.lastIndexOf('.')
        if (lastSep == -1) (EmptyPackageName, termName(fullClassName))
        else {
          import scala.language.unsafeNulls
          val packageName = termName(fullClassName.substring(0, lastSep))
          val className = termName(fullClassName.substring(lastSep + 1))
          (packageName, className)
        }
      }
      val (pkg, cls) = packageAndClass(fullClassName)
      classpath.packages.find(_.name == pkg) match {
        case Some(pkg) => pkg.tastys.find(_.simpleName == cls)
        case _         => None
      }

    def scanClass(cls: ClassSymbol)(using baseCtx: BaseContext): Unit =
      uninitialised.get(cls) match {
        case Some(classRoot) =>
          uninitialised -= cls
          if !cls.initialised then // may have been initialised by TASTy
            ClassfileParser.loadInfo(classRoot)(using baseCtx.withRoot(cls)).toTry.get
            cls.initialised = true
        case _ =>
      }

    def scanPackage(pkg: PackageClassSymbol)(using BaseContext): Unit = {
      if !searched then initPackages() // fill in classes from classpath if package was initialised by TASTy
      index.get(pkg) match {
        case Some(classes) =>
          def isNestedOrModuleClass(cd: ClassData): Boolean = {
            def isNested = {
              val name = cd.simpleName.name
              val idx = name.lastIndexOf('$', name.length - 2)
              idx >= 0 &&
              (idx + str.topLevelSuffix.length + 1 != name.length || !name.endsWith(str.topLevelSuffix))
            }
            def isModule = {
              val name = cd.simpleName.name
              name.last == '$' && name.length > 1
            }
            isNested || isModule
          }

          index -= pkg
          println(s"initialising root classes from $pkg")
          // classes.filter(!isNestedClass(_)).foreach { cls => println(s"entering class ${cls.classPart}") }
          classes.foreach { cls =>
            if !isNestedOrModuleClass(cls) then
              val clsSym = Classpaths.enterRoot(cls, pkg)
              uninitialised += (clsSym -> cls) // TODO: what if someone searches for the module class first?
          }
        case _ => // assume already loaded (possible that someone is only loading from tasty file with empty classpath)
      }
    }

    def initPackages()(using BaseContext): Unit =
      if !searched then {
        searched = true

        def enterPackages(packages: IArray[PackageData]) = {
          println(s"begin enter packages")

          // TODO: do not use fully qualified name for storing packages in decls
          val packageNameCache = mutable.HashMap.empty[TermName, TermName]

          packageNameCache.sizeHint(packages.size)

          def cached(name: TermName): TermName =
            packageNameCache.getOrElseUpdate(name, name)

          def toPackageName(parts: IndexedSeq[String]): TermName =
            if parts.isEmpty then EmptyPackageName
            else parts.view.drop(1).foldLeft(cached(termName(parts.head)))((name, p) => cached(name select termName(p)))

          val packageNames =
            packages.map(pkg => toPackageName(IArray.unsafeFromArray(pkg.name.name.split('.'))))
          val classesFor = packageNames.lazyZip(packages.map(_.classes)).toMap

          var debugPackageCount = 0

          def createSubpackages(packageName: TermName)(using BaseContext): PackageClassSymbol = {
            var currentOwner = defn.RootPackage
            for subpackageName <- packageName.subnames do
              currentOwner = baseCtx.createPackageSymbolIfNew(subpackageName, currentOwner)
              debugPackageCount += 1

            currentOwner
          }

          loader.index = Map.from(for pkg <- packageNames yield createSubpackages(pkg) -> classesFor(pkg))

          // println(s"init classpath with:\n${classes.map(_.className).mkString("\n")}")
          // println(s"init classpath with packages:\n${debugPackages.map(_.toDebugString).mkString("\n")}")
          println(s"end enter packages: $debugPackageCount")
        }

        enterPackages(classpath.packages)
      }
  }
}
