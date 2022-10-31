package tastyquery

import Contexts.*
import Paths.*
import Symbols.*

import tastyquery.testutil.TestPlatform
import scala.concurrent.Future
import tastyquery.Classpaths.Classpath
import scala.concurrent.ExecutionContext.Implicits.global

class ClasspathEntrySuite extends UnrestrictedUnpicklingSuite:

  def scala3ClasspathEntry = TestPlatform.scala3ClasspathEntry()

  def lookupSyms(entry: AnyRef)(using Context): IArray[Symbol] =
    IArray.from(ctx.findSymbolsByClasspathEntry(entry))

  testWithContext("scala-library-by-entry") {

    val MirrorClass = resolve(name"scala" / name"deriving" / tname"Mirror")
    val JavaLangString = resolve(name"java" / name"lang" / tname"String")

    val syms = lookupSyms(scala3ClasspathEntry)

    assert(syms.size < 300, s"scala 3 library has unexpected root symbols, found ${syms.size}")

    assert(syms.exists(_ == MirrorClass))
    assert(!syms.exists(_ == JavaLangString))

  }

  testWithContext("lookup-by-entry-reentrant") {
    // WHITEBOX: test that we can lookup by classpath entries twice without
    // caching problems

    val MirrorClass = resolve(name"scala" / name"deriving" / tname"Mirror")

    val syms1, syms2 = lookupSyms(scala3ClasspathEntry)

    assert(syms1.exists(_ == MirrorClass))
    assert(syms2.exists(_ == MirrorClass))

  }

  testWithContextDerived("load-symbols-from-derived-classpath") {
    // WHITEBOX: The context here was loaded from a classpath derived from another one.
    resolve(name"scala" / name"deriving" / tname"Mirror")
  }

  def testWithContextDerived(name: String)(using munit.Location)(body: Context ?=> Unit): Unit =
    testWithContextDerived(new munit.TestOptions(name))(body)

  def testWithContextDerived(options: munit.TestOptions)(using munit.Location)(body: Context ?=> Unit): Unit =
    test(options) {
      for derivedClasspath <- testClasspathDerived yield
        val ctx = Contexts.init(derivedClasspath)
        body(using ctx)
    }

  lazy val testClasspathDerived: Future[Classpath] = TestPlatform.loadDerivedClasspath()
