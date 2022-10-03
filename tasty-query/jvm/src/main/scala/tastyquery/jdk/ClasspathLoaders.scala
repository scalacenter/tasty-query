package tastyquery.jdk

import java.io.{InputStream, IOException}
import java.nio.file.*
import java.nio.file.attribute.BasicFileAttributes
import java.util.jar.{JarEntry, JarFile}

import scala.collection.mutable
import scala.util.Using

import tastyquery.Classpaths.*

object ClasspathLoaders {

  enum FileKind(val ext: String):
    case Class extends FileKind("class")
    case Tasty extends FileKind("tasty")

    def appliesTo(path: Path): Boolean =
      path.getFileName().nn.toString().nn.endsWith("." + ext)
  end FileKind

  object FileKind:
    lazy val All: Set[FileKind] = Set(Class, Tasty)
  end FileKind

  def splitClasspath(raw: String): List[Path] = {
    import scala.language.unsafeNulls
    raw.split(java.io.File.pathSeparator).toList.map(Paths.get(_))
  }

  def read(classpath: List[Path]): Classpath =
    read(classpath, FileKind.All)

  def read(classpath: List[Path], kinds: Set[FileKind]): Classpath = {
    def load(): IArray[PackageData] = {

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

      def streamPackages() =
        classpathToEntries(classpath).flatMap { entry =>
          val map = {
            entry.walkFiles(kinds.toSeq*) { (kind, fileWithExt, path, bytes) =>
              val (s"$file.${kind.`ext`}") = fileWithExt: @unchecked
              val bin = binaryName(file)
              val (packageName, simpleName) = classAndPackage(bin)
              kind match {
                case FileKind.Class =>
                  packageName -> ClassData(simpleName, path, bytes)
                case FileKind.Tasty =>
                  packageName -> TastyData(simpleName, path, bytes)
              }
            }
          }
          map.get(FileKind.Class).getOrElse(Nil) ++ map.get(FileKind.Tasty).getOrElse(Nil)
        }

      def compress(packages: List[(String, ClassData | TastyData)]) = {
        given Ordering[ClassData] = Ordering.by(_.binaryName)
        given Ordering[TastyData] = Ordering.by(_.binaryName)
        given Ordering[PackageData] = Ordering.by(_.dotSeparatedName)
        val groupedPackages = IArray.from(packages).groupMap((pkg, _) => pkg)((_, data) => data)
        val pkgs = groupedPackages.map { (pkg, classAndTastys) =>
          val (classes, tastys) = classAndTastys.partitionMap {
            case classData: ClassData => Left(classData)
            case tastyData: TastyData => Right(tastyData)
          }
          PackageData(pkg, classes.sorted, tastys.sorted)
        }
        IArray.from(pkgs).sorted
      }

      compress(streamPackages())
    }
    val cp = load()
    Classpath.from(cp)
  }

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

  private def classpathToEntries(classpath: List[Path]): List[ClasspathEntry] =
    classpath.flatMap(e =>
      if (Files.exists(e)) {
        if (Files.isDirectory(e)) ClasspathEntry.Directory(e) :: Nil
        else if (e.getFileName().toString().endsWith(".jar")) ClasspathEntry.Jar(e) :: Nil
        else Nil
      } else {
        Nil
      }
    )

  enum ClasspathEntry {
    case Jar(path: Path)
    case Directory(path: Path)

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
      }
  }

}
