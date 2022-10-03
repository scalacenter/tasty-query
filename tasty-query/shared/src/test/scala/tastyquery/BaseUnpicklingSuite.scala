package tastyquery

import scala.concurrent.Future

import tastyquery.reader.classfiles.Classpaths.Classpath
import tastyquery.testutil.TestPlatform

abstract class BaseUnpicklingSuite extends munit.FunSuite {
  lazy val testClasspath: Future[Classpath] = TestPlatform.loadClasspath()
}
