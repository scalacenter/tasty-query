package tastyquery.testutil

import scala.concurrent.Future

import tastyquery.reader.classfiles.Classpaths.Classpath

transparent inline def testPlatform(using testPlatform: TestPlatform): testPlatform.type = testPlatform

trait TestPlatform {
  def loadClasspath(): Future[Classpath]
}
