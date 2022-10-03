package tastyquery.testutil

import scala.scalajs.js
import scala.scalajs.js.annotation.*

import scala.concurrent.Future

import tastyquery.reader.classfiles.Classpaths.Classpath

object TestPlatform:
  def loadClasspath(): Future[Classpath] =
    nodejs.NodeJSTestPlatform.loadClasspath()

  def readResourceCodeFile(relPath: String): String =
    nodejs.NodeJSTestPlatform.readResourceCodeFile(relPath)
end TestPlatform
