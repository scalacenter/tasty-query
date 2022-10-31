package tastyquery.testutil

import scala.scalajs.js
import scala.scalajs.js.annotation.*

import scala.concurrent.Future

import tastyquery.Classpaths.*

object TestPlatform:
  def loadClasspath(): Future[Classpath] =
    nodejs.NodeJSTestPlatform.loadClasspath()

  def loadDerivedClasspath(): Future[Classpath] =
    nodejs.NodeJSTestPlatform.loadDerivedClasspath()

  def scala3ClasspathEntry(): AnyRef =
    nodejs.NodeJSTestPlatform.scala3ClasspathEntry()

  def readResourceCodeFile(relPath: String): String =
    nodejs.NodeJSTestPlatform.readResourceCodeFile(relPath)
end TestPlatform
