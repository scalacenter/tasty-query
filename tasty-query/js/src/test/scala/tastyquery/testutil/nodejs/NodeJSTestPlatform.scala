package tastyquery.testutil.nodejs

import scala.scalajs.js
import scala.scalajs.js.annotation.*

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future

import tastyquery.reader.classfiles.Classpaths.Classpath

object NodeJSTestPlatform:
  private val TestClassPathEnvVar = "TASTY_TEST_CLASSPATH"
  private val ResourceCodeEnvVar = "TASTY_TEST_SOURCES"

  private def getEnvVar(name: String): String =
    js.Dynamic.global.process.env.selectDynamic(name).asInstanceOf[String]

  private lazy val classpath: Future[Classpath] =
    val cpEnvVar = getEnvVar(TestClassPathEnvVar)
    val stringEntries = cpEnvVar.split(';').toList

    tastyquery.nodejs.ClasspathLoaders.read(stringEntries)
  end classpath

  def loadClasspath(): Future[Classpath] =
    classpath

  def readResourceCodeFile(relPath: String): String =
    val path = getEnvVar(ResourceCodeEnvVar).nn + "/" + relPath
    NodeFS.readFileSync(path, "utf-8")

  private object NodeFS:
    @js.native
    @JSImport("fs", "readFileSync")
    def readFileSync(path: String, encoding: String): String = js.native
  end NodeFS
end NodeJSTestPlatform
