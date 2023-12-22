package tastyquery

/** Representation of the contents of classpaths. */
object Classpaths:
  /** The representation of an entire classpath.
    *
    * Classpaths are made of a sequence of entries (where order is relevant).
    * Each entry contains a set of packages, and packages contain set of class
    * information files.
    */
  type Classpath = List[ClasspathEntry]

  /** One entry of the classpath.
    *
    * A `ClasspathEntry` must have a meaningful `equals` and `hashCode`, which
    * must reflect the identity of the entry (not necessarily the reference
    * identity). Its equality is notably used by
    * [[Contexts.Context.findSymbolsByClasspathEntry]].
    *
    * Users of a `ClasspathEntry` and its components may consider them to be
    * idempotent.
    *
    * All the methods of `ClasspathEntry` and its components may throw
    * `java.io.IOException`s to indicate I/O errors.
    *
    * A `ClasspathEntry` is encouraged to be thread-safe, along with all its
    * components, but it is not a strong requirement. Implementations that are
    * thread-safe should be documented as such. [[Contexts.Context]]s created
    * only from thread-safe `ClasspathEntry`s are thread-safe themselves.
    *
    * Implementations of this class are encouraged to define a `toString()`
    * method that helps identifying the entry for debugging purposes.
    */
  trait ClasspathEntry:
    /** Lists all the packages available in this entry, including nested packages.
      *
      * This method must not return two items with the same [[PackageData.dotSeparatedName]].
      *
      * Subsequent calls to `listAllPackages` may return the same instances of
      * [[PackageData]], but need not do so.
      */
    def listAllPackages(): List[PackageData]
  end ClasspathEntry

  /** Information about one package within a [[ClasspathEntry]].
    *
    * Implementations of this class are encouraged to define a `toString()`
    * method that helps identifying the package and its enclosing classpath
    * entry for debugging purposes.
    */
  trait PackageData:
    /** The fully-qualified name of the package represented by this `PackageData`. */
    val dotSeparatedName: String

    /** Lists all the files containing class information in this package (but not nested packages).
      *
      * Class information is found in `.class` files and `.tasty` files. For
      * any binary name `X`, if there is both an `X.class` and an `X.tasty`,
      * they must be returned as part of the same [[ClassData]].
      *
      * This method must not return two items with the same [[ClassData.binaryName]].
      *
      * Subsequent calls to `listAllClassDatas` and [[getClassDataByBinaryName]]
      * may return the same instances of [[ClassData]], but need not do so.
      */
    def listAllClassDatas(): List[ClassData]

    /** Get the [[ClassData]] associated with the given `binaryName` in this package, if it exists.
      *
      * Returns `None` if neither `binaryName.class` nor `binaryName.tasty` exists.
      *
      * Subsequent calls to `getClassDataByBinaryName` and [[listAllClassDatas]]
      * may return the same instance of [[ClassData]], but need not do so.
      */
    def getClassDataByBinaryName(binaryName: String): Option[ClassData]
  end PackageData

  /** Information about one class within a [[PackageData]].
    *
    * When both a `.class` file and a `.tasty` file exist for a given binary
    * name, they are represented by the same instance of `ClassData`.
    *
    * Implementations of this class are encouraged to define a `toString()`
    * method that helps identifying the class and its enclosing package and
    * classpath entry for debugging purposes.
    */
  trait ClassData:
    /** The binary name of the class information represented by this `ClassData`.
      *
      * It is the name of the file(s) without the `.class` or `.tasty` extension.
      */
    val binaryName: String

    /** Tests whether this class information has an associated `.tasty` file. */
    def hasTastyFile: Boolean

    /** Reads the contents of the `.tasty` file associated with this class information. */
    def readTastyFileBytes(): IArray[Byte]

    /** Tests whether this class information has an associated `.class` file. */
    def hasClassFile: Boolean

    /** Reads the contents of the `.class` file associated with this class information. */
    def readClassFileBytes(): IArray[Byte]
  end ClassData

  /** In-memory representation of classpath entries.
    *
    * In-memory classpath entries are thread-safe.
    */
  object InMemory:
    import Classpaths as generic

    /** A thread-safe, immutable classpath entry. */
    final class ClasspathEntry(debugString: String, val packages: List[PackageData]) extends generic.ClasspathEntry:
      override def toString(): String = debugString

      def listAllPackages(): List[generic.PackageData] = packages
    end ClasspathEntry

    /** A thread-safe, immutable package information within a classpath entry. */
    final class PackageData(debugString: String, val dotSeparatedName: String, val classes: List[ClassData])
        extends generic.PackageData:
      private lazy val byBinaryName = classes.map(c => c.binaryName -> c).toMap

      override def toString(): String = debugString

      def listAllClassDatas(): List[generic.ClassData] = classes

      def getClassDataByBinaryName(binaryName: String): Option[generic.ClassData] = byBinaryName.get(binaryName)
    end PackageData

    /** A thread-safe, immutable class information within a classpath entry. */
    final class ClassData(
      debugString: String,
      val binaryName: String,
      val tastyFileBytes: Option[IArray[Byte]],
      val classFileBytes: Option[IArray[Byte]]
    ) extends generic.ClassData:
      override def toString(): String = debugString

      def hasTastyFile: Boolean = tastyFileBytes.isDefined

      def readTastyFileBytes(): IArray[Byte] = tastyFileBytes.get

      def hasClassFile: Boolean = classFileBytes.isDefined

      def readClassFileBytes(): IArray[Byte] = classFileBytes.get

      def combineWith(that: ClassData): ClassData =
        require(
          this.binaryName == that.binaryName,
          s"cannot combine two ClassData for different binary names ${this.binaryName} and ${that.binaryName}"
        )
        ClassData(
          debugString,
          binaryName,
          this.tastyFileBytes.orElse(that.tastyFileBytes),
          this.classFileBytes.orElse(that.classFileBytes)
        )
      end combineWith
    end ClassData
  end InMemory
end Classpaths
