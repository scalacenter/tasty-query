package tastyquery

/** In-memory representation of the contents of classpaths. */
object Classpaths:
  /** Contains class data and tasty data for a given package. */
  final class PackageData(val dotSeparatedName: String, val classes: IArray[ClassData], val tastys: IArray[TastyData]):
    override def toString(): String = s"PackageData($dotSeparatedName)"

  /** In-memory representation of a `.class` file.
    *
    * `binaryName` is the file name without the `.class` extension.
    */
  final class ClassData(val binaryName: String, val debugPath: String, val bytes: IArray[Byte]):
    override def toString(): String = s"ClassData($binaryName, $debugPath)"

  /** In-memory representation of a `.tasty` file.
    *
    * `binaryName` is the file name without the `.class` extension.
    */
  final class TastyData(val binaryName: String, val debugPath: String, val bytes: IArray[Byte]):
    override def toString(): String = s"TastyData($binaryName, $debugPath)"

  /** In-memory representation of an entire classpath.
    *
    * A [[Classpath]] can be given to [[Contexts.Context.initialize]] to create a
    * [[Contexts.Context]]. The latter gives semantic access to all the
    * definitions on the classpath.
    */
  final class Classpath(val entries: IArray[Classpath.Entry]):

    /** Returns the concatenation of this classpath with `other`.
      * This is useful for structural sharing of [[Classpath.Entry Classpath Entries]]. e.g. in the following example
      * the standard library is loaded once and shared between two classpaths:
      * ```scala
      * val stdLibCp = ClasspathLoaders.read(standardLibraryPaths)
      * val libV101Cp = ClasspathLoaders.read(List(Paths.get("path/to/lib-1.0.1.jar"))) ++ stdLibCp
      * val libV102Cp = ClasspathLoaders.read(List(Paths.get("path/to/lib-1.0.2.jar"))) ++ stdLibCp
      * ```
      */
    def ++(other: Classpath): Classpath = Classpath(entries ++ other.entries)

    /** Filter a classpath so it only contains roots that match the given binary names. */
    def withFilter(binaryNames: List[String]): Classpath =

      def packageAndClass(binaryName: String): (String, String) =
        val lastSep = binaryName.lastIndexOf('.')
        if lastSep == -1 then ("", binaryName)
        else
          import scala.language.unsafeNulls
          val packageName = binaryName.substring(0, lastSep)
          val className = binaryName.substring(lastSep + 1)
          (packageName, className)

      def filterEntry(entry: Classpath.Entry, lookup: Map[String, List[String]]) =
        val packages = entry.packages.collect {
          case pkg if lookup.contains(pkg.dotSeparatedName) =>
            val tastys = pkg.tastys.filter(t => lookup(pkg.dotSeparatedName).contains(t.binaryName))
            val classes = pkg.classes.filter(c => lookup(pkg.dotSeparatedName).contains(c.binaryName))
            PackageData(pkg.dotSeparatedName, classes, tastys)
        }
        Classpath.Entry(packages)

      val formatted = binaryNames.map(packageAndClass)
      val lookup = formatted.groupMap((pkg, _) => pkg)((_, cls) => cls)
      val filtered = entries.map(filterEntry(_, lookup))
      Classpath(filtered)
    end withFilter
  end Classpath

  /** Factory object for [[Classpath]] instances. */
  object Classpath {

    /** An entry (directory or jar file) of a [[Classpath]].
      *
      * You can lookup all symbols originating from a particular [[Classpath.Entry]]
      * with [[Contexts.Context.findSymbolsByClasspathEntry ctx.findSymbolsByClasspathEntry]].
      *
      * For example:
      *
      * ```scala
      * val classpath = ClasspathLoaders.read(myLibraryPath :: stdLibPaths)
      * given Context = Contexts.init(classpath)
      * val myLibSyms = ctx.findSymbolsByClasspathEntry(classpath.entries.head)
      * ```
      */
    final class Entry(val packages: IArray[PackageData])
  }
end Classpaths
