package tastyquery.testutil.jdk

import java.nio.file.*

import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global

import tastyquery.jdk.ClasspathLoaders
import tastyquery.reader.classfiles.Classpaths.Classpath
import tastyquery.testutil.TestPlatform

object JavaTestPlatform {
  private val TestClassPathEnvVar = "TASTY_TEST_CLASSPATH"
  private val ResourceCodeEnvVar = "TASTY_TEST_SOURCES"

  private lazy val classpath: Classpath =
    val stringEntries = System.getenv(TestClassPathEnvVar).nn.split(';').toList

    val entries: List[Path] =
      for stringEntry <- stringEntries yield stringEntry match
        case s"jrt:/modules/$module/" =>
          FileSystems.getFileSystem(java.net.URI.create("jrt:/")).nn.getPath("modules", module).nn
        case _ =>
          Paths.get(stringEntry).nn

    ClasspathLoaders.read(entries)
  end classpath

  def loadClasspath(): Future[Classpath] =
    Future(classpath)

  def readResourceCodeFile(relPath: String): String =
    val path = System.getenv(ResourceCodeEnvVar).nn + "/" + relPath
    scala.io.Source.fromFile(path).mkString
}
