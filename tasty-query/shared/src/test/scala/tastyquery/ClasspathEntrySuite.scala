package tastyquery

import Contexts.*
import Paths.*
import Symbols.*

import tastyquery.testutil.TestPlatform
import scala.concurrent.Future
import tastyquery.Classpaths.Classpath
import scala.concurrent.ExecutionContext.Implicits.global

class ClasspathEntrySuite extends UnrestrictedUnpicklingSuite:

  def scala3ClasspathEntry(using Context) = ctx.classloader.classpath.entries(TestPlatform.scala3ClasspathIndex)

  def lookupSyms(entry: Classpath.Entry)(using Context): IArray[Symbol] =
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

    val syms1 = lookupSyms(scala3ClasspathEntry)
    val syms2 = lookupSyms(scala3ClasspathEntry) // explicit second lookup

    assert(syms1.exists(_ == MirrorClass))
    assert(syms2.exists(_ == MirrorClass))

  }

end ClasspathEntrySuite
