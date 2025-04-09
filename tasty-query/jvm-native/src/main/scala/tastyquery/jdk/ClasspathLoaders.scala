package tastyquery.jdk

import java.io.{InputStream, IOException}
import java.nio.file.*
import java.nio.file.attribute.BasicFileAttributes
import java.util.jar.{JarEntry, JarFile}

import scala.collection.mutable
import scala.util.Using

import tastyquery.Classpaths.*

/** Classpath loaders using the JDK API.
  *
  * This API is specific to the JVM. It is not available in Scala.js.
  */
object ClasspathLoaders {

  private enum FileKind(val ext: String):
    case Class extends FileKind("class")
    case Tasty extends FileKind("tasty")

    def appliesTo(path: Path): Boolean =
      path.getFileName().nn.toString().nn.endsWith("." + ext)
  end FileKind

  private object FileKind:
    lazy val All: Set[FileKind] = Set(Class, Tasty)
  end FileKind

  /** Reads the contents of a classpath.
    *
    * Entries can be directories or jar files. Non-existing entries are
    * ignored.
    *
    * This method will synchronously read the contents of all `.class` and
    * `.tasty` files on the classpath.
    *
    * The resulting [[Classpaths.Classpath]] can be given to [[Contexts.Context.initialize]]
    * to create a [[Contexts.Context]]. The latter gives semantic access to all
    * the definitions on the classpath.
    *
    * The entries of the resulting [[Classpaths.Classpath]] are all guaranteed
    * to be thread-safe.
    *
    * @note the resulting [[Classpaths.ClasspathEntry ClasspathEntry]] entries of
    *       the returned [[Classpaths.Classpath]] correspond to the elements of `classpath`.
    */
  def read(classpath: List[Path]): Classpath =
    read(classpath, FileKind.All)

  private def read(classpath: List[Path], kinds: Set[FileKind]): Classpath =

    def classAndPackage(binaryName: String): (String, String) = {
      val lastSep = binaryName.lastIndexOf('.')
      if (lastSep == -1) ("", binaryName)
      else
        import scala.language.unsafeNulls
        val packageName = binaryName.substring(0, lastSep)
        val simpleName = binaryName.substring(lastSep + 1)
        (packageName, simpleName)
    }

    def binaryName(classFile: String): String =
      /* Replace *both* slashes and backslashes, because the Java file APIs
       * are permissive in what they manipulate, so it's possible to get,
       * especially on Windows.
       */
      classFile.replace('/', '.').nn.replace('\\', '.').nn
    end binaryName

    def compressPackageData(
      entryDebugString: String,
      data: List[(String, InMemory.ClassData)]
    ): List[InMemory.PackageData] =
      val groupedPackages = data.groupMap((pkg, _) => pkg)((_, data) => data)
      groupedPackages.map { (packageName, allClassDatas) =>
        val packageDebugString = entryDebugString + ":" + packageName
        val mergedClassDatas =
          allClassDatas.groupMapReduce(_.binaryName)(identity)(_.combineWith(_)).valuesIterator.toList
        InMemory.PackageData(packageDebugString, packageName, mergedClassDatas)
      }.toList
    end compressPackageData

    def toEntry(entryDebugString: String, entry: ClasspathEntryKind): InMemory.ClasspathEntry =
      val map = entry.walkFiles(kinds.toSeq*) { (kind, fileWithExt, path, bytes) =>
        val (s"$file.${kind.`ext`}") = fileWithExt: @unchecked
        val bin = binaryName(file)
        val (packageName, simpleName) = classAndPackage(bin)
        kind match {
          case FileKind.Class =>
            packageName -> InMemory.ClassData(path, simpleName, None, Some(bytes))
          case FileKind.Tasty =>
            packageName -> InMemory.ClassData(path, simpleName, Some(bytes), None)
        }
      }
      val packageDatas: List[InMemory.PackageData] =
        compressPackageData(
          entryDebugString,
          map.get(FileKind.Class).getOrElse(Nil) ++ map.get(FileKind.Tasty).getOrElse(Nil)
        )
      InMemory.ClasspathEntry(entryDebugString, packageDatas)
    end toEntry

    classpathToEntries(classpath).map(toEntry)
  end read

  private def loadBytes(fileStream: InputStream): IArray[Byte] = {
    val bytes = new java.io.ByteArrayOutputStream()
    val buffer = new Array[Byte](1024)
    while
      val read = fileStream.read(buffer)
      if read >= 0 then bytes.write(buffer, 0, read)
      read >= 0
    do ()
    IArray.from(bytes.toByteArray().nn)
  }

  private def classpathToEntries(classpath: List[Path]): List[(String, ClasspathEntryKind)] =
    for e <- classpath yield
      val entryKind =
        if Files.exists(e) then
          if Files.isDirectory(e) then ClasspathEntryKind.Directory(e)
          else if e.getFileName().toString().endsWith(".jar") then ClasspathEntryKind.Jar(e)
          else throw IllegalArgumentException("Illegal classpath entry: " + e)
        else ClasspathEntryKind.Empty
      e.toString() -> entryKind
  end classpathToEntries

  private enum ClasspathEntryKind {
    case Jar(path: Path)
    case Directory(path: Path)
    case Empty

    def walkFiles[T](kinds: FileKind*)(op: (FileKind, String, String, IArray[Byte]) => T): Map[FileKind, List[T]] =
      this match {
        case Jar(path) =>
          val exts0 = kinds.map(kind => s".${kind.ext}")
          def getFullPath(filename: String): String = s"$path:$filename"
          val matching = mutable.HashMap.from(kinds.map(kind => kind -> mutable.ListBuffer.empty[JarEntry]))
          Using(JarFile(path.toFile())) { jar =>
            val results = {
              import scala.language.unsafeNulls
              def matches(je: JarEntry): Boolean = {
                val name = je.getName
                exts0.exists(name.endsWith)
              }
              val stream = jar.stream
              stream.forEach { je =>
                if matches(je) then
                  matching(kinds.find { kind =>
                    val name = je.getName
                    name.endsWith(kind.ext)
                  }.get) += je
              }
              matching.map { case kind -> jes =>
                kind ->
                  jes.toList.map { je =>
                    Using(jar.getInputStream(je))(is =>
                      op(kind, je.getName(), getFullPath(je.getName()), loadBytes(is))
                    ).get
                  }
              }.toMap
            }
            results
          }.get

        case Directory(path) =>
          import scala.language.unsafeNulls

          val matching = mutable.HashMap.from(kinds.map(kind => kind -> mutable.ListBuffer.empty[Path]))

          Files.walkFileTree(
            path,
            new FileVisitor[Path] {
              def preVisitDirectory(dir: Path, attrs: BasicFileAttributes): FileVisitResult =
                FileVisitResult.CONTINUE

              def visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult =
                for applicableKind <- kinds.find(_.appliesTo(file)) do matching(applicableKind) += file
                FileVisitResult.CONTINUE

              def visitFileFailed(file: Path, exc: IOException): FileVisitResult =
                FileVisitResult.CONTINUE

              def postVisitDirectory(dir: Path, exc: IOException): FileVisitResult =
                FileVisitResult.CONTINUE
            }
          )

          matching.map { case ext -> files =>
            ext ->
              files.toList.map { f =>
                val bytes = IArray.from(Files.readAllBytes(f))
                op(ext, path.relativize(f).toString(), f.toString(), bytes)
              }
          }.toMap

        case Empty => Map.empty
      }
  }

}
