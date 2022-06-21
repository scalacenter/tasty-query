package tastyquery

import tastyquery.testutil.{testPlatform, TestPlatform}

abstract class BaseUnpicklingSuite extends munit.FunSuite {
  given TestPlatform = tastyquery.testutil.jdk.JavaTestPlatform // TODO: make abstract so we can test scala.js

  lazy val testClasspath = testPlatform.loadClasspath()
}
