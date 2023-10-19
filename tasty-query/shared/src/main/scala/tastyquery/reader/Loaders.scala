package tastyquery.reader

import scala.collection.mutable
import scala.reflect.NameTransformer

import tastyquery.Classpaths.*
import tastyquery.Contexts
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*

import tastyquery.reader.ReaderContext.rctx
import tastyquery.reader.classfiles.ClassfileParser
import tastyquery.reader.classfiles.ClassfileParser.{ClassKind, InnerClassDecl, Resolver}
import tastyquery.reader.tasties.TastyUnpickler

private[tastyquery] object Loaders {

  class MissingTopLevelTasty(root: Loader.Root) extends Exception(s"Missing TASTy for $root")
  class UnexpectedTasty(root: Loader.Root) extends Exception(s"Unexpected TASTy for $root")

  object Loader:
    private[Loaders] case class Root private[Loaders] (pkg: PackageSymbol, rootName: SimpleName):
      override def toString(): String =
        if pkg.isRootPackage || pkg.name == nme.EmptyPackageName then rootName.toString
        else pkg.displayFullName + "." + rootName.toString
  end Loader

  class Loader(val classpath: Classpath) {

    given Resolver = Resolver()

    private enum Entry:
      case ClassAndTasty(classData: ClassData, tastyData: TastyData)
      case TastyOnly(tastyData: TastyData)
      case ClassOnly(classData: ClassData, inners: IArray[ClassData])

    private type ByEntryMap = Map[Classpath.Entry, IArray[(PackageSymbol, IArray[SimpleName])]]

    private var searched = false
    private var packages: Map[PackageSymbol, IArray[PackageData]] = compiletime.uninitialized
    private var _hasGenericTuples: Boolean = compiletime.uninitialized
    private var byEntry: ByEntryMap | Null = null
    private val roots: mutable.Map[PackageSymbol, mutable.Map[SimpleName, Entry]] = mutable.HashMap.empty
    private var topLevelTastys: Map[Loader.Root, List[Tree]] = Map.empty

    private def toPackageName(dotSeparated: String): PackageFullName =
      val parts =
        if dotSeparated.isEmpty() then nme.EmptyPackageName :: Nil
        else dotSeparated.split('.').toList.map(termName(_))
      PackageFullName(parts)

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
    private def completeRoot(root: Loader.Root, entry: Entry)(using ctx: Context): Unit =
      doCompleteRoot(root, entry)(using ReaderContext(ctx))

    private def doCompleteRoot(root: Loader.Root, entry: Entry)(using ReaderContext): Unit =
      def innerClassLookup(nested: IArray[ClassData]): Map[SimpleName, ClassData] =
        val mkBinaryName: String => SimpleName =
          if root.pkg == rctx.EmptyPackage then termName(_)
          else
            val pre = root.pkg.fullName.path.mkString("/")
            bin => termName(s"$pre/$bin")
        Map.from(nested.view.map(c => mkBinaryName(c.binaryName) -> c))
      end innerClassLookup

      def inspectClass(root: Loader.Root, classData: ClassData, entry: Entry): Unit =
        ClassfileParser.readKind(root.pkg, classData) match
          case ClassKind.Scala2(structure, runtimeAnnotStart) =>
            ClassfileParser.loadScala2Class(structure, runtimeAnnotStart)
          case ClassKind.Java(structure, sig, optInnerClasses) =>
            entry match
              case Entry.ClassOnly(_, nested) =>
                val lookup = innerClassLookup(nested)
                val innerDecls =
                  ClassfileParser.loadJavaClass(root.pkg, root.rootName, structure, sig, lookup, optInnerClasses)
                if innerDecls.nonEmpty then enterInners(innerDecls, lookup)
              case _ => throw UnexpectedTasty(root)
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
            tastyData.debugPath,
            TastyUnpickler.TreeSectionUnpickler(
              unpickler.unpickle(tastyData.debugPath, new TastyUnpickler.PositionSectionUnpickler)
            )
          )
          .get
          .unpickle()
        topLevelTastys += root -> trees
      end enterTasty

      def enterInners(explore: List[InnerClassDecl], lookup: Map[SimpleName, ClassData])(using Resolver): Unit =
        def unexpectedClassKind(kind: ClassKind, inner: InnerClassDecl) =
          val fullName = s"${root.pkg.fullName.path.mkString("/")}/${inner.classData.binaryName}"
          ClassfileFormatException(s"Unexpected class kind $kind for inner class $fullName")

        explore match
          case inner :: rest =>
            ClassfileParser.readKind(inner.owner, inner.classData) match
              case ClassKind.Java(structure, sig, inners) =>
                val innerDecls = ClassfileParser.loadJavaClass(inner.owner, inner.name, structure, sig, lookup, inners)
                enterInners(rest ::: innerDecls, lookup)
              case kind => throw unexpectedClassKind(kind, inner)
          case nil =>
            ()
      end enterInners

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
    end doCompleteRoot

    /** Loads all the roots of the given `pkg`. */
    private[tastyquery] def loadAllRoots(pkg: PackageSymbol)(using Context): Unit =
      for
        entries <- roots.remove(pkg)
        (rootName, entry) <- IArray.from(entries).sortBy(_(0)) // sort for determinism.
      do completeRoot(Loader.Root(pkg, rootName), entry)
    end loadAllRoots

    /** Loads all the roots of the given `pkg` that could be package objects. */
    private[tastyquery] def loadAllPackageObjectRoots(pkg: PackageSymbol)(using Context): Unit =
      roots.get(pkg) match
        case Some(entries) =>
          val candidateNames = entries.keysIterator.filter(_.isPackageObjectName).toList.sorted // sort for determinism
          for
            rootName <- candidateNames
            entry <- entries.remove(rootName)
          do completeRoot(Loader.Root(pkg, rootName), entry)
        case None =>
          ()
    end loadAllPackageObjectRoots

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

    private def foreachEntry(data: PackageData)(f: (SimpleName, Entry) => Unit): Unit =
      def binaryNameToRootName(binaryName: String): SimpleName =
        termName(NameTransformer.decode(binaryName))

      if data.classes.isEmpty then
        for tData <- data.tastys do f(binaryNameToRootName(tData.binaryName), Entry.TastyOnly(tData))
      else
        val tastyMap = data.tastys.map(t => t.binaryName -> t).toMap
        val nestedPrefixes = data.classes.map(_.binaryName + "$")

        for cData <- data.classes do
          val binaryName = cData.binaryName

          tastyMap.get(binaryName) match
            case Some(tastyData) =>
              // #263 If there is a `.tasty` file, it is necessarily top-level
              f(binaryNameToRootName(binaryName), Entry.ClassAndTasty(cData, tastyData))

            case None =>
              /* Otherwise, it can be Scala 2 or Java. In that case, we must
               * only process top-level classes. We must include nested class
               * data regardless, because we cannot tell whether it is Java
               * or Scala 2 here.
               */
              val isTopLevel = !nestedPrefixes.exists(binaryName.startsWith(_))
              if isTopLevel then
                val nestedPrefix = binaryName + "$"
                val nestedData = data.classes.filter(_.binaryName.startsWith(nestedPrefix))
                f(binaryNameToRootName(binaryName), Entry.ClassOnly(cData, nestedData))
    end foreachEntry

    def scanPackage(pkg: PackageSymbol)(using Context): Unit = {
      require(searched)
      packages.get(pkg) match {
        case Some(datas) =>
          packages -= pkg
          val localRoots = mutable.HashMap.empty[SimpleName, Entry]
          for data <- datas do
            foreachEntry(data)(localRoots.getOrElseUpdate) // duplicate roots from later classpath entries are ignored
          roots(pkg) = localRoots
        case _ => // probably a synthetic package that only has other packages as members. (i.e. `package java`)
      }
    }

    def lookupByEntry(src: Classpath.Entry)(using Context): Option[Iterable[TermOrTypeSymbol]] =

      def lookupRoots(pkg: PackageSymbol, rootNames: IArray[SimpleName]) =
        val buf = IArray.newBuilder[TermOrTypeSymbol]
        def lookup(n: Name) =
          for case t: TermOrTypeSymbol <- pkg.getDecl(n) do buf += t
        for rootName <- rootNames do
          lookup(rootName)
          lookup(rootName.toTypeName)
          lookup(rootName.withObjectSuffix.toTypeName)
        buf.result()

      def computeLookup(map: ByEntryMap) =
        map.get(src) match
          case Some(pkgs) => Some(pkgs.view.flatMap(lookupRoots))
          case None       => None

      val localByEntry = byEntry
      if localByEntry == null then
        val newByEntry = computeByEntry()
        byEntry = newByEntry
        computeLookup(newByEntry)
      else computeLookup(localByEntry)
    end lookupByEntry

    def initPackages()(using ctx: Context): Unit =

      def loadPackages(): IArray[(PackageSymbol, PackageData)] =
        val localPackages = mutable.HashMap.empty[String, PackageSymbol]
        def createOrLookupPackage(pkgName: String): PackageSymbol =
          localPackages.getOrElseUpdate(pkgName, ctx.findPackageFromRootOrCreate(toPackageName(pkgName)))
        classpath.entries.flatMap(entry =>
          entry.packages.map(pkg => createOrLookupPackage(pkg.dotSeparatedName) -> pkg)
        )
      end loadPackages

      if !searched then
        searched = true
        packages = loadPackages().groupMap((pkg, _) => pkg)((_, data) => data)
        _hasGenericTuples =
          packages.get(defn.scalaPackage).exists(_.exists(_.tastys.exists(_.binaryName == "$times$colon")))
    end initPackages

    def hasGenericTuples: Boolean = _hasGenericTuples

    private def computeByEntry()(using Context): ByEntryMap =
      require(searched)

      val localByEntry =
        mutable.HashMap.empty[Classpath.Entry, mutable.HashMap[PackageSymbol, mutable.HashSet[SimpleName]]]
      val localSeen = mutable.HashMap.empty[PackageSymbol, mutable.HashSet[SimpleName]]
      val localPackages = mutable.HashMap.empty[String, PackageSymbol]

      def lookupPackage(pkgName: String): PackageSymbol =
        localPackages.getOrElseUpdate(pkgName, ctx.findPackageFromRoot(toPackageName(pkgName)))

      for
        entry <- classpath.entries
        pkgData <- entry.packages
      do
        val pkg = lookupPackage(pkgData.dotSeparatedName)
        foreachEntry(pkgData)((name, _) =>
          if !localSeen.getOrElseUpdate(pkg, mutable.HashSet.empty).contains(name) then
            // only enter here the first time we see this name in this package
            localSeen(pkg).add(name)
            localByEntry
              .getOrElseUpdate(entry, mutable.HashMap.empty)
              .getOrElseUpdate(pkg, mutable.HashSet.empty)
              .add(name)
        )
      end for
      localByEntry.view
        .mapValues(entries => IArray.from(entries.view.mapValues(IArray.from)))
        .toMap
    end computeByEntry
  }
}
