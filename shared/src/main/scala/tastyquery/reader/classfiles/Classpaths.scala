package tastyquery.reader.classfiles

import scala.collection.mutable

import tastyquery.Contexts
import tastyquery.Contexts.*
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Trees.Tree
import tastyquery.reader.TastyUnpickler

import ClassfileParser.ClassKind

import tastyquery.util.syntax.chaining.given

import compiletime.asMatchable

object Classpaths {

  class MissingTopLevelTasty(root: Loader.Root) extends Exception(s"Missing TASTy for ${root.fullName}")

  /** Contains class data and tasty data. `name` is a Scala identifier */
  case class PackageData(name: SimpleName, classes: IArray[ClassData], tastys: IArray[TastyData])

  /** Contains class bytes. `simpleName` is a Scala identifier */
  case class ClassData(simpleName: SimpleName, debugPath: String, bytes: IArray[Byte])

  /** Contains tasty bytes. `simpleName` is a Scala identifier */
  case class TastyData(simpleName: SimpleName, debugPath: String, bytes: IArray[Byte])

  object permissions {

    /** sentinel value, it proves that `ctx.withRoot` can only be called from `scanClass` */
    opaque type LoadRoot = Unit
    private[Classpaths] inline def withLoadRootPrivelege[T](inline op: LoadRoot ?=> T): T = op(using ())
  }

  sealed abstract class Classpath protected (val packages: IArray[PackageData]) {

    def loader[T](op: Loader => T): T = op(Loader(this))

    def withFilter(binaryNames: List[String]): Classpath =
      def packageAndClass(binaryName: String): (SimpleName, SimpleName) = {
        val lastSep = binaryName.lastIndexOf('.')
        if lastSep == -1 then (nme.EmptyPackageName, termName(binaryName))
        else {
          import scala.language.unsafeNulls
          val packageName = termName(binaryName.substring(0, lastSep))
          val className = termName(binaryName.substring(lastSep + 1))
          (packageName, className)
        }
      }
      val formatted = binaryNames.map(packageAndClass)
      val grouped = formatted.groupMap((pkg, _) => pkg)((_, cls) => cls)
      val filtered = packages.collect {
        case pkg if grouped.contains(pkg.name) =>
          val tastys = pkg.tastys.filter(t => grouped(pkg.name).contains(t.simpleName))
          val classes = pkg.classes.filter(c => grouped(pkg.name).contains(c.simpleName))
          PackageData(pkg.name, classes, tastys)
      }
      new Classpath(filtered) {}
    end withFilter
  }

  object Classpath {
    case object Empty extends Classpath(IArray.empty)

    def from(packages: IArray[PackageData]): Classpath =
      if (packages.isEmpty) Empty
      else new Classpath(packages) {}
  }

  object Loader:
    private[tastyquery] case class Root private[Classpaths] (pkg: PackageSymbol, rootName: SimpleName):
      def packages: IterableOnce[PackageSymbol] =
        (pkg #:: LazyList.from(pkg.enclosingDecls)).asInstanceOf[IterableOnce[PackageSymbol]]

      def fullName: FullyQualifiedName =
        pkg.fullName.select(rootName)

  class Loader(val classpath: Classpath) { loader =>

    private enum Entry:
      case ClassAndTasty(classData: ClassData, tastyData: TastyData)
      case TastyOnly(tastyData: TastyData)
      case ClassOnly(classData: ClassData)

    private var searched = false
    private var packages: Map[PackageSymbol, PackageData] = compiletime.uninitialized
    private val roots: mutable.Map[PackageSymbol, mutable.Map[SimpleName, Entry]] = mutable.HashMap.empty
    private var topLevelTastys: Map[Loader.Root, List[Tree]] = Map.empty

    def toPackageName(dotSeparated: String): FullyQualifiedName =
      val parts =
        if dotSeparated.isEmpty() then nme.EmptyPackageName :: Nil
        else dotSeparated.split('.').toList.map(termName(_))
      FullyQualifiedName(parts)

    /** If this is a root symbol, lookup possible top level tasty trees associated with it. */
    private[tastyquery] def topLevelTasty(rootSymbol: Symbol)(using Context): Option[List[Tree]] =
      rootSymbol.outer match
        case pkg: PackageSymbol =>
          val rootName = rootSymbol.name.toTermName.stripObjectSuffix.asSimpleName
          val root = Loader.Root(pkg, rootName)
          topLevelTastys.get(root)
        case _ => None

    /** Lookup definitions in the entry, returns true if some roots were entered matching the `rootName`. */
    private def completeRoots(root: Loader.Root, entry: Entry)(using Context): Boolean =

      def inspectClass(root: Loader.Root, classData: ClassData, entry: Entry)(
        using Context,
        permissions.LoadRoot
      ): Boolean =
        ClassfileParser.readKind(classData).toTry.get match
          case ClassKind.Scala2(structure, runtimeAnnotStart) =>
            ClassfileParser.loadScala2Class(structure, runtimeAnnotStart).toTry.get
            Contexts.initialisedRoot(root)
          case ClassKind.Java(structure, sig) =>
            ClassfileParser.loadJavaClass(root.pkg, root.rootName, structure, sig).toTry.get
            Contexts.initialisedRoot(root)
          case ClassKind.TASTy =>
            entry match
              case Entry.ClassAndTasty(_, tasty) =>
                // TODO: verify UUID of tasty matches classfile, then parse symbols
                enterTasty(root, tasty)
              case _ => throw MissingTopLevelTasty(root)
          case _ =>
            false // no initialisation step to take
      end inspectClass

      def enterTasty(root: Loader.Root, tastyData: TastyData)(using permissions.LoadRoot): Boolean =
        // TODO: test reading tree from dependency not directly queried??
        val unpickler = TastyUnpickler(tastyData.bytes)
        val trees = unpickler
          .unpickle(
            TastyUnpickler.TreeSectionUnpickler(unpickler.unpickle(new TastyUnpickler.PositionSectionUnpickler))
          )
          .get
          .unpickle(tastyData.debugPath)
        if Contexts.initialisedRoot(root) then
          topLevelTastys += root -> trees
          true
        else false
      end enterTasty

      permissions.withLoadRootPrivelege {
        entry match
          case entry: Entry.ClassOnly =>
            // Tested in `TypeSuite` - aka Java and Scala 2 dependencies
            inspectClass(root, entry.classData, entry)
          case entry: Entry.ClassAndTasty =>
            // Tested in `TypeSuite` - read Tasty file that may reference Java and Scala 2 dependencies
            // maybe we do not need to parse the class, however the classfile could be missing the TASTY attribute.
            inspectClass(root, entry.classData, entry)
          case entry: Entry.TastyOnly =>
            // Tested in `SymbolSuite`, `ReadTreeSuite`, these do not need to see class files.
            enterTasty(root, entry.tastyData)
      }
    end completeRoots

    private[tastyquery] def forceRoots(pkg: PackageSymbol)(using Context): Unit =
      for
        entries <- roots.remove(pkg)
        (rootName, entry) <- IArray.from(entries).sortBy(_(0)) // sort for determinism.
      do completeRoots(Loader.Root(pkg, rootName), entry)

    /** @return true if loaded the classes inner definitions */
    private[tastyquery] def enterRoots(pkg: PackageSymbol, name: Name)(using Context): Option[Symbol] =
      roots.get(pkg) match
        case Some(entries) =>
          val rootName = name.toTermName.stripObjectSuffix.asSimpleName
          for
            entry <- entries.remove(rootName)
            if completeRoots(Loader.Root(pkg, rootName), entry)
            resolved <- pkg.getDeclInternal(name) // should have entered some roots, now lookup the requested root
          yield resolved
        case _ => None
    end enterRoots

    /** Does not force any classes, returns a root either if root symbols are already loaded, or if there are
      * unloaded roots matching the name.
      */
    private[tastyquery] def findRoot(pkg: PackageSymbol, name: SimpleName)(using Context): Option[Loader.Root] =
      val root = Loader.Root(pkg, name)
      if Contexts.initialisedRoot(root) then Some(root)
      else // not yet forced
        roots.get(pkg) match
          case Some(entries) =>
            if entries.contains(root.rootName) then Some(root)
            else None
          case _ => None

    def scanPackage(pkg: PackageSymbol)(using Context): Unit = {
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

          val localRoots = mutable.HashMap.empty[SimpleName, Entry]

          if data.classes.isEmpty then
            for tData <- data.tastys if !isNestedOrModuleClassName(tData.simpleName) do
              localRoots += (tData.simpleName -> Entry.TastyOnly(tData))
          else
            val tastyMap = data.tastys.map(t => t.simpleName -> t).toMap
            for cData <- data.classes if !isNestedOrModuleClassName(cData.simpleName) do
              val entry =
                tastyMap.get(cData.simpleName).map(Entry.ClassAndTasty(cData, _)).getOrElse(Entry.ClassOnly(cData))
              localRoots += (cData.simpleName -> entry)

          roots(pkg) = localRoots

        case _ => // probably a synthetic package that only has other packages as members. (i.e. `package java`)
      }
    }

    def initPackages()(using ctx: Context): Unit =
      if !searched then {
        searched = true

        def enterPackages(packages: IArray[PackageData]) = {
          val packageNames = packages.map(pkg => toPackageName(pkg.name.name))

          var debugPackageCount = 0

          def createSubpackages(packageName: FullyQualifiedName)(using Context): PackageSymbol = {
            var currentOwner = defn.RootPackage
            for subpackageName <- packageName.path do
              currentOwner = ctx.createPackageSymbolIfNew(subpackageName.asSimpleName, currentOwner)
              debugPackageCount += 1

            currentOwner
          }

          loader.packages =
            Map.from(for (pkgName, data) <- packageNames.zip(packages) yield createSubpackages(pkgName) -> data)
        }

        enterPackages(classpath.packages)
      }
  }
}
