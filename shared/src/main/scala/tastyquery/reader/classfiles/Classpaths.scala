package tastyquery.reader.classfiles

import tastyquery.ast.Names.SimpleName
import scala.reflect.NameTransformer
import tastyquery.Contexts
import tastyquery.Contexts.{BaseContext, baseCtx, ctx, defn}
import scala.collection.mutable
import tastyquery.ast.Names.{TermName, nme, termName, str}
import tastyquery.ast.Symbols.PackageClassSymbol
import tastyquery.ast.Symbols.ClassSymbol
import tastyquery.ast.Symbols.DeclaringSymbol
import tastyquery.reader.TastyUnpickler

import ClassfileParser.ClassKind
import tastyquery.Contexts.ClassContext
import tastyquery.Contexts.FileContext
import tastyquery.ast.Trees.Tree

object Classpaths {

  class MissingTopLevelTasty(cls: ClassSymbol) extends Exception(s"Missing TASTy for $cls")

  /** Contains class data and tasty data. `name` is a Scala identifier */
  case class PackageData(name: SimpleName, classes: IArray[ClassData], tastys: IArray[TastyData])

  /** Contains class bytes. `simpleName` is a Scala identifier */
  case class ClassData(simpleName: SimpleName, debugPath: String, bytes: IArray[Byte])

  /** Contains tasty bytes. `simpleName` is a Scala identifier */
  case class TastyData(simpleName: SimpleName, debugPath: String, bytes: IArray[Byte])

  object permissions {

    /** sentinel value, it proves that `baseCtx.withRoot` can only be called from `scanClass` */
    opaque type LoadRoot = Unit
    private[Classpaths] inline def withLoadRootPrivelege[T](inline op: LoadRoot ?=> T): T = op(using ())
  }

  def enterRoot(root: SimpleName, owner: DeclaringSymbol)(using BaseContext): ClassSymbol = {
    val clsName = root.toTypeName
    val objclassName = clsName.toObjectName
    val objName = root

    locally {
      baseCtx.createSymbol(objName, owner)
      baseCtx.createClassSymbol(objclassName, owner)
    }
    baseCtx.createClassSymbol(clsName, owner)
  }

  sealed abstract class Classpath protected (val packages: IArray[PackageData]) {

    def loader[T](op: Loader => T): T = op(Loader(this))

  }

  object Classpath {
    case object Empty extends Classpath(IArray.empty)

    def from(packages: IArray[PackageData]): Classpath =
      if (packages.isEmpty) Empty
      else new Classpath(packages) {}
  }

  class Loader(val classpath: Classpath) { loader =>

    private enum Entry:
      case ClassAndTasty(classData: ClassData, tastyData: TastyData)
      case TastyOnly(tastyData: TastyData)
      case ClassOnly(classData: ClassData)

    private var searched = false
    private var packages: Map[PackageClassSymbol, PackageData] = compiletime.uninitialized
    private var lookup: Map[ClassSymbol, Entry] = Map.empty
    private var topLevelTastys: Map[ClassSymbol, List[Tree]] = Map.empty

    // TODO: do not use fully qualified name for storing packages in decls
    private val packageNameCache = mutable.HashMap.empty[TermName, TermName]

    def toPackageName(dotSeparated: String): TermName =
      def cached(name: TermName): TermName =
        packageNameCache.getOrElseUpdate(name, name)

      def qualified(parts: IndexedSeq[String]): TermName =
        if parts.isEmpty then nme.EmptyPackageName
        else parts.view.drop(1).foldLeft(cached(termName(parts.head)))((name, p) => cached(name select termName(p)))

      qualified(IArray.unsafeFromArray(dotSeparated.split('.')))

    private[tastyquery] def topLevelTasty(cls: ClassSymbol)(using BaseContext): Option[List[Tree]] =
      if !cls.outer.isPackage then
        println(s"No top-level tasty for $cls: it is not top-level")
        None
      else if !Contexts.initialisedRoot(cls) then
        println(s"No top-level tasty for $cls: it is not initialised")
        None
      else if cls.name.toTypeName.wrapsObjectName then
        println(s"No top-level tasty for $cls: it is an object class")
        None
      else
        topLevelTastys.get(cls) match
          case None =>
            println(s"No top-level tasty for $cls: it has no associated TASTy")
            None
          case some => some

    /** @return true if loaded the classes inner definitions */
    private[tastyquery] def scanClass(cls: ClassSymbol)(using baseCtx: BaseContext): Boolean =
      def inspectClass(classData: ClassData, entry: Entry)(using ClassContext, permissions.LoadRoot): Boolean =
        ClassfileParser.readKind(classData).toTry.get match
          case ClassKind.Scala2(structure, runtimeAnnotStart) =>
            ClassfileParser.loadScala2Class(structure, runtimeAnnotStart).toTry.get
            Contexts.initialisedRoot(cls)
          case ClassKind.Java(structure) =>
            ClassfileParser.loadJavaClass(structure).toTry.get
            Contexts.initialisedRoot(cls)
          case ClassKind.TASTy =>
            entry match
              case Entry.ClassAndTasty(_, tasty) =>
                // TODO: verify UUID of tasty matches classfile, then parse symbols
                enterTasty(tasty)(using baseCtx.withFile(cls, tasty.debugPath))
              case _ => throw MissingTopLevelTasty(cls)
          case _ =>
            false // no initialisation step to take
      end inspectClass

      def enterTasty(tastyData: TastyData)(using FileContext): Boolean =
        // TODO: test reading tree from dependency not directly queried??
        val unpickler = TastyUnpickler(tastyData.bytes)
        val trees = unpickler.unpickle(TastyUnpickler.TreeSectionUnpickler()).get.unpickle(using ctx)
        if Contexts.initialisedRoot(cls) then
          topLevelTastys += cls -> trees
          true
        else false

      // TODO: test against standalone objects, modules, etc.
      lookup.get(cls) match
        case Some(entry) =>
          permissions.withLoadRootPrivelege {
            require(!cls.initialised)
            lookup -= cls
            entry match
              case entry: Entry.ClassOnly =>
                // Tested in `TypeSuite` - aka Java and Scala 2 dependencies
                inspectClass(entry.classData, entry)(using baseCtx.withRoot(cls))
              case entry: Entry.ClassAndTasty =>
                // Tested in `TypeSuite` - read Tasty file that may reference Java and Scala 2 dependencies
                // maybe we do not need to parse the class, however the classfile could be missing the TASTY attribute.
                inspectClass(entry.classData, entry)(using baseCtx.withRoot(cls))
              case entry: Entry.TastyOnly =>
                // Tested in `SymbolSuite`, `ReadTreeSuite`, these do not need to see class files.
                enterTasty(entry.tastyData)(using baseCtx.withFile(cls, entry.tastyData.debugPath))
          }

        case _ => false
    end scanClass

    def scanPackage(pkg: PackageClassSymbol)(using BaseContext): Unit = {
      require(searched)
      packages.get(pkg) match {
        case Some(data) =>
          def isNestedOrModuleClassName(cls: SimpleName): Boolean = {
            def isNested = {
              val name = cls.name
              val idx = name.lastIndexOf('$', name.length - 2)
              idx >= 0 &&
              !(idx + str.topLevelSuffix.length == name.length && name.endsWith(str.topLevelSuffix))
            }
            def isModule = {
              val name = cls.name
              name.last == '$' && name.length > 1
            }
            isNested || isModule
          }

          packages -= pkg
          println(s"initialising root classes from $pkg")

          if data.classes.isEmpty then
            for tasty <- data.tastys if !isNestedOrModuleClassName(tasty.simpleName) do
              val clsSym = Classpaths.enterRoot(tasty.simpleName, pkg)
              lookup += (clsSym -> Entry.TastyOnly(tasty))
          else
            val tastyMap = data.tastys.map(t => t.simpleName -> t).toMap
            for cls <- data.classes if !isNestedOrModuleClassName(cls.simpleName) do
              val clsSym = Classpaths.enterRoot(cls.simpleName, pkg)
              val entry =
                tastyMap.get(cls.simpleName).map(Entry.ClassAndTasty(cls, _)).getOrElse(Entry.ClassOnly(cls))
              lookup += (clsSym -> entry) // TODO: what if someone searches for the module class first?

        case _ => // assume already loaded (possible that someone is only loading from tasty file with empty classpath)
      }
    }

    def initPackages()(using baseCtx: BaseContext): Unit =
      if !searched then {
        searched = true

        def enterPackages(packages: IArray[PackageData]) = {
          println(s"begin enter packages")

          packageNameCache.sizeHint(packages.size)

          val packageNames = packages.map(pkg => toPackageName(pkg.name.name))

          var debugPackageCount = 0

          def createSubpackages(packageName: TermName)(using BaseContext): PackageClassSymbol = {
            var currentOwner = defn.RootPackage
            for subpackageName <- packageName.subnames do
              currentOwner = baseCtx.createPackageSymbolIfNew(subpackageName, currentOwner)
              debugPackageCount += 1

            currentOwner
          }

          loader.packages =
            Map.from(for (pkgName, data) <- packageNames.zip(packages) yield createSubpackages(pkgName) -> data)

          // println(s"init classpath with:\n${classes.map(_.className).mkString("\n")}")
          // println(s"init classpath with packages:\n${debugPackages.map(_.toDebugString).mkString("\n")}")
          println(s"end enter packages: $debugPackageCount")
        }

        enterPackages(classpath.packages)
      }
  }
}
