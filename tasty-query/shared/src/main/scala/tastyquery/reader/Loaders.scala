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
import tastyquery.Utils.*

import tastyquery.reader.ReaderContext.rctx
import tastyquery.reader.classfiles.{ClassfileParser, ClassfileReader}
import tastyquery.reader.classfiles.ClassfileParser.{ClassKind, InnerClassDecl, Resolver}
import tastyquery.reader.classfiles.ClassfileReader.Structure
import tastyquery.reader.tasties.TastyUnpickler

private[tastyquery] object Loaders {

  private[tastyquery] final class PackageLoadingInfo private[Loaders] (
    pkg: PackageSymbol,
    initPackageData: List[PackageData]
  ):
    private lazy val dataByBinaryName =
      val localRoots = mutable.HashMap.empty[String, ClassData]
      for packageData <- initPackageData do
        for classData <- packageData.listAllClassDatas() do
          // duplicate roots from later classpath entries are ignored
          localRoots.getOrElseUpdate(classData.binaryName, classData)
      end for
      localRoots
    end dataByBinaryName

    private type LoadedFiles = mutable.HashSet[String]

    /** Loads all the roots of the associated package. */
    def loadAllRoots()(using Context): Unit =
      given ReaderContext = ReaderContext(ctx)

      // Sort for determinism, and to make sure that outer classes always come before their inner classes
      val allNames = dataByBinaryName.keysIterator.toList.sorted

      loadingRoots { loadedFiles =>
        for rootName <- allNames do tryLoadRoot(rootName, loadedFiles)
      }

      // Upon success of loading all roots, we can throw away everything, even potential inner Java classes
      dataByBinaryName.clear()
    end loadAllRoots

    /** Loads all the roots of the associated package that could be package objects. */
    def loadAllPackageObjectRoots()(using Context): Unit =
      given ReaderContext = ReaderContext(ctx)

      def isPackageObjectBinaryName(name: String): Boolean =
        name == "package" || name.endsWith("$package")

      // Sort for determinism, and to make sure that outer classes always come before their inner classes
      val candidateNames = dataByBinaryName.keysIterator.filter(isPackageObjectBinaryName(_)).toList.sorted

      loadingRoots { loadedFiles =>
        for rootName <- candidateNames do tryLoadRoot(rootName, loadedFiles)
      }
    end loadAllPackageObjectRoots

    /** Loads the root of the associated package that would define `name`, if there is one such root. */
    def loadOneRoot(name: Name)(using Context): Unit =
      given ReaderContext = ReaderContext(ctx)

      loadingRoots { loadedFiles =>
        val binaryName = topLevelSymbolNameToRootName(name)
        tryLoadRoot(binaryName, loadedFiles)
      }
    end loadOneRoot

    private def topLevelSymbolNameToRootName(name: Name): String = name match
      case name: TypeName =>
        topLevelSymbolNameToRootName(name.toTermName)
      case ObjectClassName(objName) =>
        topLevelSymbolNameToRootName(objName)
      case name: SimpleName =>
        NameTransformer.encode(name.name)
      case _ =>
        throw IllegalStateException(s"Invalid top-level symbol name ${name.toDebugString}")
    end topLevelSymbolNameToRootName

    private def loadingRoots[A](op: LoadedFiles => A): A =
      val loadedFiles = mutable.HashSet.empty[String]
      val result = op(loadedFiles)

      // Upon success, remove all the loaded files so that we do not attempt to load them again later
      dataByBinaryName --= loadedFiles

      result
    end loadingRoots

    private def tryLoadRoot(binaryName: String, loadedFiles: LoadedFiles)(using ReaderContext): Unit =
      dataByBinaryName.get(binaryName) match
        case None =>
          ()
        case Some(classData) =>
          // Avoid reading inner classes that we already loaded through their outer classes.
          if loadedFiles.add(binaryName) then
            if classData.hasTastyFile then doLoadTasty(classData)
            else if !doLoadClassFile(classData, loadedFiles) then
              /* Oops, maybe we will need this one later, if it is a (non-local)
               * inner class of another Java class.
               * Removing it from loadedFiles so that we do not throw away the file.
               */
              loadedFiles -= binaryName
    end tryLoadRoot

    private lazy val fullBinaryNamePrefix: String =
      if pkg.isEmptyPackage then ""
      else pkg.fullName.path.mkString("", "/", "/")

    def doLoadClassFile(classData: ClassData, loadedFiles: LoadedFiles)(using ReaderContext): Boolean =
      val structure = ClassfileReader.readStructure(pkg, classData)
      val kind = ClassfileParser.detectClassKind(structure)
      kind match
        case ClassKind.Scala2 =>
          ClassfileParser.loadScala2Class(structure)
          true
        case ClassKind.Java =>
          doLoadJavaTopLevelClass(classData, structure, loadedFiles)
          true
        case ClassKind.TASTy =>
          throw TastyFormatException(s"Missing TASTy file for class ${classData.binaryName} in package $pkg")
        case ClassKind.ScalaArtifact =>
          // Always ignore; we can consider it loaded because nobody will ever need it
          true
        case ClassKind.JavaInnerOrArtifact =>
          // Ignore at the top-level, but we cannot throw it away because it might be needed as an inner class
          false
    end doLoadClassFile

    private def doLoadJavaTopLevelClass(classData: ClassData, structure: Structure, loadedFiles: LoadedFiles)(
      using ReaderContext
    ): Unit =
      // The resolver for this top-level class and all its inner classes
      given Resolver = Resolver()

      val innerDecls = ClassfileParser.loadJavaClass(pkg, termName(classData.binaryName), structure)
      doLoadJavaInnerClasses(innerDecls, loadedFiles)
    end doLoadJavaTopLevelClass

    private def doLoadJavaInnerClasses(explore: List[InnerClassDecl], loadedFiles: LoadedFiles)(
      using ReaderContext,
      Resolver
    ): Unit =
      explore match
        case inner :: rest =>
          val innerSimpleName = inner.innerSimpleName
          val localBinaryName = inner.innerBinaryName.name.stripPrefix(fullBinaryNamePrefix)
          dataByBinaryName.get(localBinaryName) match
            case Some(innerData) if !loadedFiles.contains(localBinaryName) =>
              loadedFiles += localBinaryName
              val structure = ClassfileReader.readStructure(inner.owner, innerData)
              val innerDecls = ClassfileParser.loadJavaClass(inner.owner, innerSimpleName, structure)
              doLoadJavaInnerClasses(rest ::: innerDecls, loadedFiles)
            case _ =>
              throw ClassfileFormatException(
                s"Inner class $localBinaryName not found in package $pkg for owner ${inner.owner}"
              )
        case Nil =>
          ()
    end doLoadJavaInnerClasses

    private def doLoadTasty(classData: ClassData)(using ReaderContext): Unit =
      val unpickler = TastyUnpickler(classData.readTastyFileBytes())
      val debugPath = classData.toString()
      unpickler
        .unpickle(
          debugPath,
          TastyUnpickler.TreeSectionUnpickler(
            unpickler.unpickle(debugPath, new TastyUnpickler.PositionSectionUnpickler)
          )
        )
        .get
        .unpickle()
    end doLoadTasty
  end PackageLoadingInfo

  class Loader(val classpath: Classpath) {
    private type ByEntryMap = Map[ClasspathEntry, IArray[(PackageSymbol, IArray[String])]]

    private var initialized = false
    private var _hasGenericTuples: Boolean = false
    private val byEntry: Memo[ByEntryMap] = uninitializedMemo

    private def toPackageName(dotSeparated: String): PackageFullName =
      val parts =
        if dotSeparated.isEmpty() then nme.EmptyPackageName :: Nil
        else dotSeparated.split('.').toList.map(termName(_))
      PackageFullName(parts)

    private def rootNameToTopLevelTermSymbolName(rootName: String): SimpleName =
      termName(NameTransformer.decode(rootName))

    def lookupByEntry(src: ClasspathEntry)(using Context): Option[Iterable[TermOrTypeSymbol]] =
      def lookupRoots(pkg: PackageSymbol, rootNames: IArray[String]) =
        val buf = IArray.newBuilder[TermOrTypeSymbol]
        def lookup(n: Name) =
          for case t: TermOrTypeSymbol <- pkg.getDecl(n) do buf += t
        for rootName <- rootNames do
          val possibleTermName = rootNameToTopLevelTermSymbolName(rootName)
          lookup(possibleTermName)
          lookup(possibleTermName.toTypeName)
          lookup(possibleTermName.withObjectSuffix.toTypeName)
        buf.result()

      def computeLookup(map: ByEntryMap) =
        map.get(src) match
          case Some(pkgs) => Some(pkgs.view.flatMap(lookupRoots))
          case None       => None

      val localByEntry = memoized(byEntry) {
        computeByEntry()
      }
      computeLookup(localByEntry)
    end lookupByEntry

    def initPackages()(using ctx: Context): Unit =
      if initialized then throw IllegalStateException(s"Classloader was already initialized")

      initialized = true

      def loadPackages(): List[(PackageSymbol, PackageData)] =
        val localPackages = mutable.HashMap.empty[String, PackageSymbol]
        def createOrLookupPackage(pkgName: String): PackageSymbol =
          localPackages.getOrElseUpdate(pkgName, ctx.findPackageFromRootOrCreate(toPackageName(pkgName)))
        classpath.flatMap(entry =>
          entry.listAllPackages().map(pkg => createOrLookupPackage(pkg.dotSeparatedName) -> pkg)
        )
      end loadPackages

      for (pkg, pairs) <- loadPackages().groupBy(_._1) do
        val initPackageData = pairs.map(_._2)
        pkg.setLoadingInfo(new PackageLoadingInfo(pkg, initPackageData))

        if pkg.isScalaPackage then
          _hasGenericTuples = initPackageData.exists(_.getClassDataByBinaryName("$times$colon").isDefined)
      end for
    end initPackages

    def hasGenericTuples: Boolean = _hasGenericTuples

    private def computeByEntry()(using Context): ByEntryMap =
      val localByEntry =
        mutable.HashMap.empty[ClasspathEntry, mutable.HashMap[PackageSymbol, mutable.HashSet[String]]]
      val localSeen = mutable.HashMap.empty[PackageSymbol, mutable.HashSet[String]]
      val localPackages = mutable.HashMap.empty[String, PackageSymbol]

      def lookupPackage(pkgName: String): PackageSymbol =
        localPackages.getOrElseUpdate(pkgName, ctx.findPackageFromRoot(toPackageName(pkgName)))

      for
        entry <- classpath
        pkgData <- entry.listAllPackages()
      do
        val pkg = lookupPackage(pkgData.dotSeparatedName)
        val localSeenForThisPackage = localSeen.getOrElseUpdate(pkg, mutable.HashSet.empty)

        for classData <- pkgData.listAllClassDatas() do
          val localBinaryName = classData.binaryName

          // only enter here the first time we see this name in this package,
          // i.e., exclude names that we found in this package in earlier class path entries
          if localSeenForThisPackage.add(localBinaryName) then
            localByEntry
              .getOrElseUpdate(entry, mutable.HashMap.empty)
              .getOrElseUpdate(pkg, mutable.HashSet.empty)
              .add(localBinaryName)
        end for
      end for

      localByEntry.view
        .mapValues(entries => IArray.from(entries.view.mapValues(IArray.from)))
        .toMap
    end computeByEntry
  }
}
