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
  final class ClassData(
    val binaryName: String,
    val debugPath: String,
    val bytes: IArray[Byte],
    private[tastyquery] val src: AnyRef
  ):
    override def toString(): String = s"ClassData($binaryName, $debugPath)"

  /** In-memory representation of a `.tasty` file.
    *
    * `binaryName` is the file name without the `.class` extension.
    */
  final class TastyData(
    val binaryName: String,
    val debugPath: String,
    val bytes: IArray[Byte],
    private[tastyquery] val src: AnyRef
  ):
    override def toString(): String = s"TastyData($binaryName, $debugPath)"

  /** In-memory representation of an entire classpath.
    *
    * A [[Classpath]] can be given to [[Contexts.init]] to create a
    * [[Contexts.Context]]. The latter gives semantic access to all the
    * definitions on the classpath.
    */
  final class Classpath private (val packages: IArray[PackageData]):
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
      val filtered = packages.collect {
        case pkg if grouped.contains(pkg.dotSeparatedName) =>
          val tastys = pkg.tastys.filter(t => grouped(pkg.dotSeparatedName).contains(t.binaryName))
          val classes = pkg.classes.filter(c => grouped(pkg.dotSeparatedName).contains(c.binaryName))
          PackageData(pkg.dotSeparatedName, classes, tastys)
      }
      new Classpath(filtered)
    end withFilter
  end Classpath

  /** Factory object for [[Classpath]] instances. */
  object Classpath {

    /** Constructs an instance of [[Classpath]] with the given [[PackageData]]s. */
    def from(packages: IArray[PackageData]): Classpath =
      new Classpath(packages)
  }
end Classpaths
