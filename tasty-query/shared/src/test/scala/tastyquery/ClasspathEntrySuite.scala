package tastyquery

import tastyquery.Classpaths.*
import tastyquery.Contexts.*
import tastyquery.Symbols.*

import tastyquery.testutil.TestPlatform

class ClasspathEntrySuite extends UnrestrictedUnpicklingSuite:

  def scala3ClasspathEntry(using Context): ClasspathEntry =
    ctx.internalClasspathForTestsOnly(TestPlatform.scala3ClasspathIndex)

  def lookupSyms(entry: ClasspathEntry)(using Context): IArray[Symbol] =
    IArray.from(ctx.findSymbolsByClasspathEntry(entry))

  testWithContext("scala-library-by-entry") {
    val MirrorClass = ctx.findTopLevelClass("scala.deriving.Mirror")

    val syms = lookupSyms(scala3ClasspathEntry)

    assert(syms.exists(_ == MirrorClass))
    assert(!syms.exists(_ == defn.StringClass))

  }

  testWithContext("lookup-by-entry-single") {
    val MirrorClass = ctx.findTopLevelClass("scala.deriving.Mirror")

    val syms = lookupSyms(scala3ClasspathEntry)

    assert(syms.exists(_ == MirrorClass))
  }

  testWithContext("lookup-by-entry-reentrant") {
    // WHITEBOX: test performance impact of reentrant lookup

    val MirrorClass = ctx.findTopLevelClass("scala.deriving.Mirror")

    def lookupMirror() =
      val syms = lookupSyms(scala3ClasspathEntry)
      assert(syms.exists(_ == MirrorClass))

    for _ <- 1 to 50 do lookupMirror()

  }

end ClasspathEntrySuite
