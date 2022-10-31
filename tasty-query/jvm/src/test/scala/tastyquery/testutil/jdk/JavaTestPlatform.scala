package tastyquery.testutil.jdk

import java.nio.file.*

import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global

import tastyquery.Classpaths.*

import tastyquery.jdk.ClasspathLoaders

object JavaTestPlatform {
  private val TestClassPathEnvVar = "TASTY_TEST_CLASSPATH"
  private val ResourceCodeEnvVar = "TASTY_TEST_SOURCES"

  private lazy val classpathEntries: List[String] =
    System.getenv(TestClassPathEnvVar).nn.split(';').toList

  private lazy val classpath: Classpath =
    val entries: List[Path] =
      for stringEntry <- classpathEntries yield stringEntry match
        case s"jrt:/modules/$module/" =>
          FileSystems.getFileSystem(java.net.URI.create("jrt:/")).nn.getPath("modules", module).nn
        case _ =>
          Paths.get(stringEntry).nn

    ClasspathLoaders.read(entries)
  end classpath

  private lazy val scala3Entry: Path =
    Paths.get(classpathEntries.find(_.contains("scala3-library_3").nn).get).nn

  def scala3ClasspathEntry(): AnyRef =
    scala3Entry

  def loadClasspath(): Future[Classpath] =
    Future(classpath)

  def readResourceCodeFile(relPath: String): String =
    val path = System.getenv(ResourceCodeEnvVar).nn + "/" + relPath
    scala.io.Source.fromFile(path).mkString
}
