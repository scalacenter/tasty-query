package tastyquery.testutil

import scala.concurrent.Future

import tastyquery.reader.classfiles.Classpaths.Classpath

object TestPlatform:
  def loadClasspath(): Future[Classpath] =
    jdk.JavaTestPlatform.loadClasspath()

  def readResourceCodeFile(relPath: String): String =
    jdk.JavaTestPlatform.readResourceCodeFile(relPath)
end TestPlatform
