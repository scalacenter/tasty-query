package tastyquery.reader

import scala.collection.mutable
import scala.reflect.NameTransformer

import tastyquery.Classpaths.*
import tastyquery.Contexts
import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*

import tastyquery.reader.classfiles.ClassfileParser
import tastyquery.reader.classfiles.ClassfileParser.ClassKind
import tastyquery.reader.tasties.TastyUnpickler

private[tastyquery] object Loaders {

  class MissingTopLevelTasty(root: Loader.Root) extends Exception(s"Missing TASTy for ${root.fullName}")

  object Loader:
    private[Loaders] case class Root private[Loaders] (pkg: PackageSymbol, rootName: SimpleName):
      def fullName: FullyQualifiedName =
        pkg.fullName.select(rootName)
  end Loader

  class Loader(val classpath: Classpath) { loader =>

    private enum Entry:
      case ClassAndTasty(classData: ClassData, tastyData: TastyData)
      case TastyOnly(tastyData: TastyData)
      case ClassOnly(classData: ClassData)

    private var searched = false
    private var packages: Map[PackageSymbol, PackageData] = compiletime.uninitialized
    private val roots: mutable.Map[PackageSymbol, mutable.Map[SimpleName, Entry]] = mutable.HashMap.empty
    private var topLevelTastys: Map[Loader.Root, List[Tree]] = Map.empty

    private def toPackageName(dotSeparated: String): FullyQualifiedName =
      val parts =
        if dotSeparated.isEmpty() then nme.EmptyPackageName :: Nil
        else dotSeparated.split('.').toList.map(termName(_))
      FullyQualifiedName(parts)

    /** If this is a root symbol, lookup possible top level tasty trees associated with it. */
    private[tastyquery] def topLevelTasty(rootSymbol: Symbol)(using Context): Option[List[Tree]] =
      rootSymbol.owner match
        case pkg: PackageSymbol =>
          val rootName = rootSymbol.name.toTermName.stripObjectSuffix.asSimpleName
          val root = Loader.Root(pkg, rootName)
          topLevelTastys.get(root)
        case _ => None

    /** Completes a root by reading the corresponding entry.
      *
      * Zero to many new declarations can be added to `root.pkg` as a result.
      *
      * In any case, no new declarations can ever be found for the given root
      * after this method.
      */
    private def completeRoot(root: Loader.Root, entry: Entry)(using Context): Unit =
      def inspectClass(root: Loader.Root, classData: ClassData, entry: Entry): Unit =
        ClassfileParser.readKind(classData) match
          case ClassKind.Scala2(structure, runtimeAnnotStart) =>
            ClassfileParser.loadScala2Class(structure, runtimeAnnotStart)
          case ClassKind.Java(structure, sig) =>
            ClassfileParser.loadJavaClass(root.pkg, root.rootName, structure, sig)
          case ClassKind.TASTy =>
            entry match
              case Entry.ClassAndTasty(_, tasty) =>
                // TODO: verify UUID of tasty matches classfile, then parse symbols
                enterTasty(root, tasty)
              case _ => throw MissingTopLevelTasty(root)
          case ClassKind.Artifact =>
            () // no initialisation step to take
      end inspectClass

      def enterTasty(root: Loader.Root, tastyData: TastyData): Unit =
        // TODO: test reading tree from dependency not directly queried??
        val unpickler = TastyUnpickler(Array.from(tastyData.bytes))
        val trees = unpickler
          .unpickle(
            TastyUnpickler.TreeSectionUnpickler(unpickler.unpickle(new TastyUnpickler.PositionSectionUnpickler))
          )
          .get
          .unpickle(tastyData.debugPath)
        topLevelTastys += root -> trees
      end enterTasty

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
    end completeRoot

    /** Loads all the roots of the given `pkg`. */
    private[tastyquery] def loadAllRoots(pkg: PackageSymbol)(using Context): Unit =
      for
        entries <- roots.remove(pkg)
        (rootName, entry) <- IArray.from(entries).sortBy(_(0)) // sort for determinism.
      do completeRoot(Loader.Root(pkg, rootName), entry)
    end loadAllRoots

    /** Loads the root of the given `pkg` that would define `name`, if there is one such root.
      *
      * When this method returns `true`, it is not guaranteed that the
      * particular `name` corresponds to a `Symbol`. But when it returns
      * `false`, there is a guarantee that no new symbol with the given `name`
      * was loaded.
      *
      * Whether this method returns `true` or `false`, any subsequent call to
      * `loadRoot` with the same arguments will return `false`.
      *
      * @return
      *   `true` if a root was loaded, `false` otherwise.
      */
    private[tastyquery] def loadRoot(pkg: PackageSymbol, name: Name)(using Context): Boolean =
      roots.get(pkg) match
        case Some(entries) =>
          val rootName = name.toTermName.stripObjectSuffix.asSimpleName
          entries.remove(rootName) match
            case Some(entry) =>
              completeRoot(Loader.Root(pkg, rootName), entry)
              true
            case None =>
              false
        case None =>
          false
    end loadRoot

    def scanPackage(pkg: PackageSymbol)(using Context): Unit = {
      require(searched)
      packages.get(pkg) match {
        case Some(data) =>
          def isNestedOrModuleClassName(name: String): Boolean = {
            def isNested = {
              val idx = name.lastIndexOf('$', name.length - 2)
              idx >= 0 &&
              !(idx + str.topLevelSuffix.length == name.length && name.endsWith(str.topLevelSuffix))
            }
            def isModule =
              name.last == '$' && name.length > 1
            isNested || isModule
          }

          packages -= pkg

          val localRoots = mutable.HashMap.empty[SimpleName, Entry]

          if data.classes.isEmpty then
            for
              tData <- data.tastys
              decodedName = NameTransformer.decode(tData.binaryName)
              if !isNestedOrModuleClassName(decodedName)
            do localRoots += (SimpleName(decodedName) -> Entry.TastyOnly(tData))
          else
            val tastyMap = data.tastys.map(t => t.binaryName -> t).toMap
            for
              cData <- data.classes
              decodedName = NameTransformer.decode(cData.binaryName)
              if !isNestedOrModuleClassName(decodedName)
            do
              val entry =
                tastyMap.get(cData.binaryName).map(Entry.ClassAndTasty(cData, _)).getOrElse(Entry.ClassOnly(cData))
              localRoots += (SimpleName(decodedName) -> entry)

          roots(pkg) = localRoots

        case _ => // probably a synthetic package that only has other packages as members. (i.e. `package java`)
      }
    }

    def initPackages()(using ctx: Context): Unit =
      if !searched then
        searched = true
        val packages = classpath.packages
        val packageSymbols = packages.map(pkg => ctx.findPackageFromRootOrCreate(toPackageName(pkg.dotSeparatedName)))
        loader.packages = Map.from(packageSymbols.zip(packages))
  }
}
