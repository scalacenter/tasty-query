package tastyquery.jdk

import java.nio.file.Files
import java.nio.file.Paths
import java.io.InputStream
import tastyquery.ast.Trees.Tree
import java.util.jar.JarFile
import org.apache.commons.io.FileUtils
import java.io.File
import scala.jdk.CollectionConverters.*
import tastyquery.reader.classfiles.Classpaths.{Classpath, PackageData, ClassData, TastyData}
import org.apache.commons.io.IOUtils
import java.nio.file.FileSystems
import tastyquery.ast.Names.{SimpleName, termName, nme}
import scala.util.Using
import scala.collection.mutable
import java.nio.file.Path
import java.util.jar.JarEntry
import tastyquery.ast.Names
import scala.reflect.NameTransformer

object ClasspathLoaders {

  enum FileKind {

    case Class, Tasty

    lazy val ext: String = this match
      case FileKind.Class => "class"
      case FileKind.Tasty => "tasty"

  }

  def splitClasspath(raw: String): List[String] = {
    import scala.language.unsafeNulls
    raw.split(File.pathSeparator).toList
  }

  def read(classpath: List[String], kinds: Set[FileKind]): Classpath = {
    def load(): IArray[PackageData] = {

      val dirSep = {
        import scala.language.unsafeNulls
        val fs = FileSystems.getDefault
        fs.getSeparator
      }

      def classAndPackage(binaryName: SimpleName): (SimpleName, SimpleName) = {
        val name = binaryName.name
        val lastSep = name.lastIndexOf('.')
        if (lastSep == -1) (nme.EmptyPackageName, termName(NameTransformer.decode(name)))
        else
          import scala.language.unsafeNulls
          val pre = name.substring(0, lastSep)
          val packageName = pre.split('.').map(NameTransformer.decode).mkString(".")
          val simpleName = NameTransformer.decode(name.substring(lastSep + 1))
          (termName(packageName), termName(simpleName))
      }

      def binaryName(classFile: String): SimpleName = {
        import scala.language.unsafeNulls
        termName(classFile.replace(dirSep, "."))
      }

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

      def compress(packages: List[(SimpleName, ClassData | TastyData)]) = {
        given Ordering[ClassData] = Ordering.by(_.simpleName)
        given Ordering[TastyData] = Ordering.by(_.simpleName)
        given Ordering[PackageData] = Ordering.by(_.name)
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
    println(s"load class data")
    val cp = load()
    val totalClassMB = cp.map(_.classes.map(_.bytes).map(_.size: BigInt).sum).sum / 1024 / 1024
    val totalTastyMB = cp.map(_.tastys.map(_.bytes).map(_.size: BigInt).sum).sum / 1024 / 1024
    println(s"loaded class data: ${cp.map(_.classes.size).sum} classes, $totalClassMB MB")
    println(s"loaded tasty data: ${cp.map(_.tastys.size).sum} tastys, $totalTastyMB MB")
    println(s"packages: ${cp.map(_.name).mkString("\n", "\n", "")}")
    Classpath.from(cp)
  }

  private def loadBytes(fileStream: InputStream): IArray[Byte] = {
    val bytes = {
      import scala.language.unsafeNulls
      IOUtils.toByteArray(fileStream)
    }
    IArray.from(bytes)
  }

  private def classpathToEntries(classpath: List[String]): List[ClasspathEntry] =
    classpath.flatMap(e =>
      if (Files.exists(Paths.get(e))) {
        if (e.endsWith(".jar")) ClasspathEntry.Jar(e) :: Nil
        else if (Files.isDirectory(Paths.get(e))) ClasspathEntry.Directory(e) :: Nil
        else Nil
      } else {
        Nil
      }
    )

  enum ClasspathEntry {
    case Jar(path: String)
    case Directory(path: String)

    def walkFiles[T](kinds: FileKind*)(op: (FileKind, String, String, IArray[Byte]) => T): Map[FileKind, List[T]] =
      this match {
        case Jar(path) =>
          val exts0 = kinds.map(kind => s".${kind.ext}")
          def getFullPath(filename: String): String = s"$path:$filename"
          val matching = mutable.HashMap.from(kinds.map(kind => kind -> mutable.ListBuffer.empty[JarEntry]))
          Using(JarFile(path)) { jar =>
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
          def getClassName(f: File): Path = {
            val dirp = Paths.get(path)
            dirp.relativize(f.toPath)
          }
          val matching = mutable.HashMap.from(kinds.map(kind => kind -> mutable.ListBuffer.empty[File]))
          val matched = FileUtils.listFiles(new File(path), kinds.map(_.ext).toArray, true)
          matched.forEach { f =>
            val kind = kinds.find { kind =>
              val name = f.getName
              name.endsWith(kind.ext)
            }.get
            matching(kind) += f
          }
          matching.map { case ext -> files =>
            ext ->
              files.toList.map { f =>
                Using(FileUtils.openInputStream(f))(is =>
                  op(ext, getClassName(f).toString, f.getAbsolutePath(), loadBytes(is))
                ).get
              }
          }.toMap
      }
  }

}
