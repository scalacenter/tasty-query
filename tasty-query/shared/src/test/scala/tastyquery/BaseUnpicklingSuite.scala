package tastyquery

import scala.concurrent.Future

import tastyquery.Classpaths.*

import tastyquery.testutil.TestPlatform

abstract class BaseUnpicklingSuite extends munit.FunSuite {
  lazy val testClasspath: Future[Classpath] = TestPlatform.loadClasspath()

  override def munitTimeout = scala.concurrent.duration.Duration.Inf
}
