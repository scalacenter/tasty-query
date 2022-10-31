package tastyquery

import scala.concurrent.Future
import scala.annotation.targetName

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
    * A [[Classpath]] can be given to [[Contexts.init]] to create a
    * [[Contexts.Context]]. The latter gives semantic access to all the
    * definitions on the classpath.
    *
    * [[Classpath.from]] creates a [[Classpath]] from a previous classpath, structurally sharing data.
    * To save memory usage, [[Classpath.from]] should always be called with the most recently created [[Classpath]].
    */
  final class Classpath private (
    private[tastyquery] val db: Map[AnyRef, IArray[PackageData]],
    private[tastyquery] val entries: IArray[AnyRef] // subset of db keys
  ):

    private[tastyquery] def lookup(entry: AnyRef): Option[IArray[PackageData]] =
      db.get(entry)

    private[tastyquery] def lookupOrElse(entry: AnyRef, orElse: => IArray[PackageData]): IArray[PackageData] =
      db.getOrElse(entry, orElse)

    /** Returns a view of all the packages in this [[Classpath]], may contain duplicate package names when
      * the same package is present in multiple classpath entries.
      */
    def packages: Iterable[PackageData] = entries.view.flatMap(db(_))

    def withFilter(binaryNames: List[String]): Classpath =
      def packageAndClass(binaryName: String): (String, String) = {
        val lastSep = binaryName.lastIndexOf('.')
        if lastSep == -1 then ("", binaryName)
        else {
          import scala.language.unsafeNulls
          val packageName = binaryName.substring(0, lastSep)
          val className = binaryName.substring(lastSep + 1)
          (packageName, className)
        }
      }
      val formatted = binaryNames.map(packageAndClass)
      val grouped = formatted.groupMap((pkg, _) => pkg)((_, cls) => cls)
      val filtered = db.view.mapValues(_.collect {
        case pkg if grouped.contains(pkg.dotSeparatedName) =>
          val tastys = pkg.tastys.filter(t => grouped(pkg.dotSeparatedName).contains(t.binaryName))
          val classes = pkg.classes.filter(c => grouped(pkg.dotSeparatedName).contains(c.binaryName))
          PackageData(pkg.dotSeparatedName, classes, tastys)
      })
      Classpath(filtered.toMap, entries)
    end withFilter
  end Classpath

  /** Factory object for [[Classpath]] instances. */
  object Classpath {

    /** The classpath with no entries, used to initialise the first classpath */
    val Empty: Classpath = Classpath(Map.empty, IArray.empty)

    /** Create a new classpath from an old one that structurally shares common entries. */
    def from(old: Classpath, entries: IArray[(AnyRef, IArray[PackageData])]): Classpath =
      // db may end up with more keys than in entries - this is to prevent duplicate data when we have forked
      // classpaths. i.e. the user should always supply the previously produced classpath for maximum sharing.
      val db = old.db ++ entries.filterNot((entry, _) => old.db.contains(entry))
      Classpath(db, entries.map((entry, _) => entry))
  }
end Classpaths
