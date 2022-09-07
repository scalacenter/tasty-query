package tastyquery.testutil.jdk

import scala.util.Properties

import java.io.File
import java.nio.file.*

import tastyquery.jdk.ClasspathLoaders
import tastyquery.reader.classfiles.Classpaths.Classpath
import tastyquery.testutil.TestPlatform

object JavaTestPlatform extends TestPlatform {
  private val ResourceProperty = "test-resources"
  private val StdLibProperty = "std-library"

  private lazy val jdk: Path = {
    import scala.language.unsafeNulls

    System.getProperty("sun.boot.class.path") match
      case null =>
        // Assume jrt:/
        FileSystems.getFileSystem(java.net.URI.create("jrt:/")).nn.getPath("modules", "java.base")

      case bootClasspath =>
        val rtJarOpt = bootClasspath.split(java.io.File.pathSeparatorChar).find { path =>
          new java.io.File(path).getName() == "rt.jar"
        }
        rtJarOpt match
          case Some(rtJar) =>
            Paths.get(rtJar)
          case None =>
            throw new AssertionError(s"cannot find rt.jar in $bootClasspath")
  }

  private def resourcesDir: Path =
    Paths.get(Properties.propOrNone(ResourceProperty).get).nn

  private def stdLibPaths: List[Path] = {
    import scala.language.unsafeNulls
    Properties.propOrEmpty(StdLibProperty).split(File.pathSeparator).toList.map(Paths.get(_).nn)
  }

  def loadClasspath(): Classpath = {
    val kinds = Set(ClasspathLoaders.FileKind.Tasty, ClasspathLoaders.FileKind.Class)
    val classpath = jdk :: resourcesDir :: stdLibPaths
    ClasspathLoaders.read(classpath, kinds)
  }
}
