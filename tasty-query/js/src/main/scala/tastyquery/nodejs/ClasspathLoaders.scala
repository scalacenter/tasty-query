package tastyquery.nodejs

import scala.scalajs.js
import scala.scalajs.js.annotation.*
import scala.scalajs.js.typedarray.*

import scala.collection.mutable
import scala.concurrent.*
import scala.util.*

import tastyquery.Classpaths.*

/** Classpath loaders using the Node.js API.
  *
  * This API is specific to Scala.js when used with Node.js. It is not
  * available on the JVM nor on other Scala.js environments.
  */
object ClasspathLoaders:
  import NodeFS.*

  /** Reads the contents of a classpath.
    *
    * Entries can be directories or jar files. Non-existing entries are
    * ignored.
    *
    * This method will asynchronously read the contents of all `.class` and
    * `.tasty` files on the classpath. It returns a `Future` that will be
    * completed when all has been read into memory.
    *
    * The resulting [[Classpaths.Classpath]] can be given to [[Contexts.init]]
    * to create a [[Contexts.Context]]. The latter gives semantic access to all
    * the definitions on the classpath.
    *
    * `old` should be the previous classpath created by this method (or defaults to [[Classpath.Empty]]).
    *  Using the previous classpath allows to share already loaded classpath data when possible.
    */
  def read(classpath: List[String], old: Classpath = Classpath.Empty)(using ExecutionContext): Future[Classpath] =
    def replaceEntry(entry: String, compute: => Future[Seq[FileContent]]) =
      val data = old.lookup(entry) match
        case Some(packages) => Future.successful(Right(packages))
        case None           => compute.map(Left(_))
      data.map(entry -> _)

    val allFilesFuture: Future[List[(String, Either[Seq[FileContent], IArray[PackageData]])]] = Future
      .traverse(classpath) { entry =>
        cbFuture[Stats](stat(entry, _)).transformWith {
          case Success(stat) if stat.isDirectory() =>
            replaceEntry(entry, fromDirectory(entry, ""))

          case Success(_) if entry.endsWith(".jar") =>
            replaceEntry(entry, fromJarFile(entry))

          case Success(_) =>
            throw new IllegalArgumentException("Illegal classpath entry: " + entry)

          case Failure(MatchableJSException(e: js.Error)) if isNotFound(e) =>
            Future.successful(entry -> Right(IArray.empty))

          case Failure(t) =>
            throw t
        }
      }

    def compressPackages(allFiles: Seq[FileContent]): Iterable[PackageData] =
      allFiles
        .groupMap[String, ClassData | TastyData](_.packagePath) { fileContent =>
          val isClassFile = fileContent.name.endsWith(".class")
          val binaryName =
            if isClassFile then fileContent.name.stripSuffix(".class")
            else fileContent.name.stripSuffix(".tasty")
          if isClassFile then ClassData(binaryName, fileContent.debugPath, fileContent.content)
          else TastyData(binaryName, fileContent.debugPath, fileContent.content)
        }
        .map { (packagePath, classAndTastys) =>
          val packageName = packagePath.replace('/', '.').nn
          val (classes, tastys) = classAndTastys.partitionMap {
            case classData: ClassData => Left(classData)
            case tastyData: TastyData => Right(tastyData)
          }
          PackageData(packageName, IArray.from(classes.sortBy(_.binaryName)), IArray.from(tastys.sortBy(_.binaryName)))
        }

    for allEntries <- allFilesFuture yield
      val compressedEntries =
        for (entry, allFiles) <- allEntries
        yield entry -> allFiles.fold(fa => IArray.from(compressPackages(fa)), identity)
      Classpath.from(old, IArray.from(compressedEntries))
  end read

  private def fromDirectory(dir: String, relPath: String)(implicit ec: ExecutionContext): Future[Seq[FileContent]] =
    cbFuture[js.Array[Dirent]](readdir(dir, ReadDirOpt, _)).flatMap { entries =>
      val (dirs, files) = entries.toSeq.partition(_.isDirectory())

      val subdirFiles = Future.traverse(dirs) { e =>
        fromDirectory(join(dir, e.name), join(relPath, e.name))
      }

      val irFileNames = files.map(_.name).filter(isClassOrTasty)
      val directFiles = Future.traverse(irFileNames) { n =>
        val path = join(dir, n)
        cbFuture[Uint8Array](readFile(path, _)).map { content =>
          val contentAsInt8Array = new Int8Array(content.buffer)
          FileContent(relPath, n, path, IArray.from(contentAsInt8Array.toArray))
        }
      }

      for {
        sdf <- subdirFiles
        df <- directFiles
      } yield sdf.flatten ++ df
    }
  end fromDirectory

  private def isNotFound(e: js.Error): Boolean =
    (e.asInstanceOf[js.Dynamic].code: Any) == "ENOENT"

  private def fromJarFile(path: String)(using ExecutionContext): Future[List[FileContent]] =
    for
      arr <- cbFuture[Uint8Array](readFile(path, _))
      zip <- JSZip.loadAsync(arr).toFuture
      files <- loadFromZip(path, zip)
    yield files.toList
  end fromJarFile

  private def loadFromZip(jarPath: String, obj: JSZip.JSZip)(
    implicit ec: ExecutionContext
  ): Future[Iterator[FileContent]] =
    val entries = obj.files.valuesIterator
      .filter(e => isClassOrTasty(e.name) && !e.dir)

    def splitPackagePathAndName(relPath: String): (String, String) =
      val lastSlash = relPath.lastIndexOf('/')
      if lastSlash < 0 then ("", relPath)
      else (relPath.substring(0, lastSlash).nn, relPath.substring(lastSlash + 1).nn)

    Future.traverse(entries) { entry =>
      entry.async(JSZipInterop.arrayBuffer).toFuture.map { buf =>
        val (packagePath, name) = splitPackagePathAndName(entry.name)
        new FileContent(packagePath, name, s"$jarPath:${entry.name}", IArray.from(new Int8Array(buf).toArray))
      }
    }
  end loadFromZip

  private def isClassOrTasty(name: String): Boolean =
    name.endsWith(".class") || name.endsWith(".tasty")

  private class FileContent(val packagePath: String, val name: String, val debugPath: String, val content: IArray[Byte])

  private object MatchableJSException:
    def unapply(x: js.JavaScriptException): Some[Matchable] =
      Some(x.exception.asInstanceOf[Matchable])
  end MatchableJSException

  private object JSZipInterop:
    val arrayBuffer: String = "arraybuffer"
  end JSZipInterop

  @js.native
  @JSImport("jszip", JSImport.Default)
  private object JSZip extends js.Object:
    trait JSZip extends js.Object:
      val files: js.Dictionary[ZipObject]
    end JSZip

    trait ZipObject extends js.Object:
      val name: String
      val dir: Boolean
      def async(tpe: JSZipInterop.arrayBuffer.type): js.Promise[ArrayBuffer]
    end ZipObject

    def loadAsync(data: Uint8Array): js.Promise[JSZip] = js.native
  end JSZip
end ClasspathLoaders
