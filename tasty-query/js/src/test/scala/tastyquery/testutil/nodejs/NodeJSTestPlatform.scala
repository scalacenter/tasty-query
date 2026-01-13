package tastyquery.testutil.nodejs

import scala.scalajs.js
import scala.scalajs.js.annotation.*

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future

import tastyquery.Classpaths.*

object NodeJSTestPlatform:
  private val TestClassPathEnvVar = "TASTY_TEST_CLASSPATH"
  private val ResourceCodeEnvVar = "TASTY_TEST_SOURCES"

  private def getEnvVar(name: String): String =
    js.Dynamic.global.process.env.selectDynamic(name).asInstanceOf[String]

  private lazy val classpathEntries: List[String] =
    val cpEnvVar = getEnvVar(TestClassPathEnvVar)
    cpEnvVar.split(';').toList

  private lazy val classpath: Future[Classpath] =
    tastyquery.nodejs.ClasspathLoaders.read(classpathEntries)

  def loadClasspath(): Future[Classpath] =
    classpath

  lazy val scala3ClasspathIndex: Int =
    classpathEntries.indexWhere(_.contains("scala3-library_3"))

  def readResourceCodeFile(relPath: String): String =
    val path = getEnvVar(ResourceCodeEnvVar) + "/" + relPath
    NodeFS.readFileSync(path, "utf-8")

  private object NodeFS:
    @js.native
    @JSImport("fs", "readFileSync")
    def readFileSync(path: String, encoding: String): String = js.native
  end NodeFS
end NodeJSTestPlatform
