package tastyquery.testutil

import scala.concurrent.Future

import tastyquery.Classpaths.*

object TestPlatform:
  def loadClasspath(): Future[Classpath] =
    native.ScalaNativeTestPlatform.loadClasspath()

  def scala3ClasspathIndex: Int =
    native.ScalaNativeTestPlatform.scala3ClasspathIndex

  def readResourceCodeFile(relPath: String): String =
    native.ScalaNativeTestPlatform.readResourceCodeFile(relPath)
end TestPlatform
