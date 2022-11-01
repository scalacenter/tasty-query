package tastyquery

import Contexts.*
import Paths.*
import Symbols.*

import tastyquery.testutil.TestPlatform
import tastyquery.Classpaths.Classpath

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

  testWithContext("lookup-by-entry-single") {
    val MirrorClass = resolve(name"scala" / name"deriving" / tname"Mirror")

    val syms = lookupSyms(scala3ClasspathEntry)

    assert(syms.exists(_ == MirrorClass))
  }

  testWithContext("lookup-by-entry-reentrant") {
    // WHITEBOX: test performance impact of reentrant lookup

    val MirrorClass = resolve(name"scala" / name"deriving" / tname"Mirror")

    def lookupMirror() =
      val syms = lookupSyms(scala3ClasspathEntry)
      assert(syms.exists(_ == MirrorClass))

    for _ <- 1 to 50 do lookupMirror()

  }

end ClasspathEntrySuite
