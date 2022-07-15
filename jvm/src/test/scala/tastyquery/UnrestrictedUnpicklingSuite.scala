package tastyquery

import tastyquery.Contexts.Context

abstract class UnrestrictedUnpicklingSuite extends BaseUnpicklingSuite {
  def testWithContext(name: String)(using munit.Location)(body: Context ?=> Unit): Unit =
    testWithContext(new munit.TestOptions(name))(body)

  def testWithContext(options: munit.TestOptions)(using munit.Location)(body: Context ?=> Unit): Unit =
    test(options) {
      val ctx = Contexts.init(testClasspath)
      body(using ctx)
    }
}
