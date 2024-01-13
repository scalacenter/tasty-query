package tastyquery

import scala.concurrent.ExecutionContext.Implicits.global

import tastyquery.Contexts.*

abstract class UnrestrictedUnpicklingSuite extends BaseUnpicklingSuite {
  import UnrestrictedUnpicklingSuite.*

  /** Set this to true to stress-test thread-safety by using a common `Context` across all test suites. */
  private final val useParallelTesting = false

  def testWithContext(name: String)(using munit.Location)(body: Context ?=> Unit): Unit =
    testWithContext(new munit.TestOptions(name))(body)

  def testWithContext(options: munit.TestOptions)(using munit.Location)(body: Context ?=> Unit): Unit =
    test(options) {
      if useParallelTesting then
        // use the common context
        for ctx <- commonContextForParallelTesting yield body(using ctx)
      else
        // create an isolated context
        for classpath <- testClasspath yield
          val ctx = Context.initialize(classpath)
          body(using ctx)
      end if
    }
}

object UnrestrictedUnpicklingSuite:
  private lazy val commonContextForParallelTesting =
    tastyquery.testutil.TestPlatform.loadClasspath().map(Context.initialize(_))
end UnrestrictedUnpicklingSuite
