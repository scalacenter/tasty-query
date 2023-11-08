package tastyquery

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Symbols.*
import tastyquery.Traversers.*
import tastyquery.Trees.*
import tastyquery.Types.*

/** Tests that are applied generically on the entire test classpath. */
class WholeClasspathSuite extends UnrestrictedUnpicklingSuite:

  testWithContext("all-symbol-resolutions") {
    /* Test that we can resolve the `.symbol` of all the `Ident`s and `Select`s
     * within the test-sources and standard library.
     */

    var successCount = 0
    val errorsBuilder = List.newBuilder[String]

    def testSelect(tree: TermReferenceTree): Unit =
      try
        tree.symbol
        tree.referenceType match
          case tpe: NamedType if tpe.prefix != NoPrefix =>
            successCount += 1
          case _ =>
            // too "easy"; don't count that as a success
            ()
      catch
        case ex: MemberNotFoundException =>
          val displayPos =
            if tree.pos.hasLineColumnInformation then s":${tree.pos.pointLine}:${tree.pos.pointColumn}"
            else ""
          val prefixDetails = ex.prefix match
            case prefix: SingletonType => s" (${prefix.showBasic}: ${prefix.superType.showBasic})"
            case prefix: Type          => s" (${prefix.showBasic})"
            case _                     => ""

          errorsBuilder += s"${tree.pos.sourceFile.path}$displayPos: ${ex.getMessage()}$prefixDetails"
    end testSelect

    def walkTree(tree: Tree): Unit =
      new Traversers.TreeTraverser {
        override def traverse(tree: Tree): Unit = tree match
          case tree: TermReferenceTree =>
            super.traverse(tree)
            testSelect(tree)
          case _ =>
            super.traverse(tree)
      }.traverse(tree)
    end walkTree

    // Ignore LazyVals.scala because it contains references to sun.misc, which is not in java.base
    val RuntimeLazyValsClass = ctx.findTopLevelModuleClass("scala.runtime.LazyVals")

    def walk(pkg: PackageSymbol): Unit =
      for sym <- pkg.declarations do
        sym match
          case sym: PackageSymbol                              => walk(sym)
          case sym: ClassSymbol if sym != RuntimeLazyValsClass => sym.tree.foreach(walkTree(_))
          case _                                               => ()
    end walk

    walk(defn.RootPackage)

    val errors = errorsBuilder.result()
    if errors.nonEmpty then
      fail(errors.mkString("Could not resolve the `symbol` of some trees on the classpath:\n", "\n", "\n"))

    // As of this writing, there were 15293 successes
    assert(clue(successCount) > 15000)
  }

end WholeClasspathSuite
