package tastyquery

import tastyquery.Contexts.BaseContext

abstract class UnrestrictedUnpicklingSuite extends BaseUnpicklingSuite {
  def testWithContext(name: String)(using munit.Location)(body: BaseContext ?=> Unit): Unit =
    testWithContext(new munit.TestOptions(name))(body)

  def testWithContext(options: munit.TestOptions)(using munit.Location)(body: BaseContext ?=> Unit): Unit =
    test(options) {
      val ctx = Contexts.init(testClasspath)
      body(using ctx)
    }
}
