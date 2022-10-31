package tastyquery

import Contexts.*
import Paths.*
import Symbols.*

import tastyquery.testutil.TestPlatform

class ClasspathEntrySuite extends UnrestrictedUnpicklingSuite:

  def scala3ClasspathEntry = TestPlatform.scala3ClasspathEntry()

  def lookupSyms(entry: AnyRef)(using Context): Iterable[Symbol] =
    ctx.findPackagesByClasspathEntry(entry).flatMap { (_, entries) =>
      entries
    }

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
