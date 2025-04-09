package tastyquery.testutil.native

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future

import tastyquery.Classpaths.*

object ScalaNativeTestPlatform:
  private val TestClassPathEnvVar = "TASTY_TEST_CLASSPATH"
  private val ResourceCodeEnvVar = "TASTY_TEST_SOURCES"

  private def getEnvVar(name: String): String =
    sys.env
      .get(name)
      .getOrElse("")

  private lazy val classpathEntries: List[String] =
    val cpEnvVar = getEnvVar(TestClassPathEnvVar)
    cpEnvVar.split(';').toList

  private lazy val classpath: Future[Classpath] =
    // Use the JDK implementation which should be compatible with Scala Native
    val paths = classpathEntries.map(path => java.nio.file.Paths.get(path))
    val res = tastyquery.jdk.ClasspathLoaders.read(paths)
    Future.successful(res)

  def loadClasspath(): Future[Classpath] =
    classpath

  lazy val scala3ClasspathIndex: Int =
    classpathEntries.indexWhere(_.contains("scala3-library_3"))

  def readResourceCodeFile(relPath: String): String =
    val path = getEnvVar(ResourceCodeEnvVar) + "/" + relPath

    // Read file using Scala Native's file I/O capabilities via scala.io.Source
    val source = scala.io.Source.fromFile(path)
    try source.mkString
    finally source.close()
end ScalaNativeTestPlatform
