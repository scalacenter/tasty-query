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
    private[tastyquery] case class Root private[Loaders] (pkg: PackageSymbol, rootName: SimpleName):
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
      rootSymbol.owner match
        case pkg: PackageSymbol =>
          val rootName = rootSymbol.name.toTermName.stripObjectSuffix.asSimpleName
          val root = Loader.Root(pkg, rootName)
          topLevelTastys.get(root)
        case _ => None

    /** Lookup definitions in the entry, returns true if some roots were entered matching the `rootName`. */
    private def completeRoots(root: Loader.Root, entry: Entry)(using Context): Boolean =

      def inspectClass(root: Loader.Root, classData: ClassData, entry: Entry): Boolean =
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

      def enterTasty(root: Loader.Root, tastyData: TastyData): Boolean =
        // TODO: test reading tree from dependency not directly queried??
        val unpickler = TastyUnpickler(Array.from(tastyData.bytes))
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
        val packageSymbols = packages.map(pkg => ctx.createPackageSymbolIfNew(toPackageName(pkg.dotSeparatedName)))
        loader.packages = Map.from(packageSymbols.zip(packages))
  }
}