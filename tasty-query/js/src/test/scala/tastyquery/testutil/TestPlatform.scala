package tastyquery.testutil

import scala.scalajs.js
import scala.scalajs.js.annotation.*

import scala.concurrent.Future

import tastyquery.Classpaths.*

object TestPlatform:
  def loadClasspath(): Future[Classpath] =
    nodejs.NodeJSTestPlatform.loadClasspath()

  def scala3ClasspathIndex: Int =
    nodejs.NodeJSTestPlatform.scala3ClasspathIndex

  def readResourceCodeFile(relPath: String): String =
    nodejs.NodeJSTestPlatform.readResourceCodeFile(relPath)
end TestPlatform
