package tastyquery

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Symbols.*
import tastyquery.Traversers.*
import tastyquery.Trees.*
import tastyquery.Types.*

/** Tests that are applied generically on the entire test classpath. */
class WholeClasspathSuite extends UnrestrictedUnpicklingSuite:
  import WholeClasspathSuite.*

  private def forEveryTopLevelClassSymbol(op: ClassSymbol => Unit)(using Context): Unit =
    def walk(pkg: PackageSymbol): Unit =
      for sym <- pkg.declarations do
        sym match
          case sym: PackageSymbol => walk(sym)
          case sym: ClassSymbol   => op(sym)
          case _                  => ()
    end walk

    walk(defn.RootPackage)
  end forEveryTopLevelClassSymbol

  private def forEveryTopLevelClassDef(filter: ClassSymbol => Boolean)(op: ClassDef => Unit)(using Context): Unit =
    forEveryTopLevelClassSymbol { sym =>
      if filter(sym) then sym.tree.foreach(op)
    }
  end forEveryTopLevelClassDef

  private def traverseEveryTopLevelClassDef(filter: ClassSymbol => Boolean)(traverser: TreeTraverser)(
    using Context
  ): Unit =
    forEveryTopLevelClassDef(filter)(traverser.traverse(_))

  testWithContext("all-symbol-resolutions") {
    /* Test that we can resolve the `.symbol` of all the `Ident`s and `Select`s
     * within the test-sources and standard library.
     */

    val tracker = new Tracker

    def testSelect(tree: TermReferenceTree): Unit =
      try
        tree.symbol
        tree.referenceType match
          case tpe: NamedType if tpe.prefix != NoPrefix =>
            tracker.registerSuccess()
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

          tracker.addError(s"${tree.pos.sourceFile.path}$displayPos: ${ex.getMessage()}$prefixDetails")
    end testSelect

    val traverser =
      new Traversers.TreeTraverser {
        override def traverse(tree: Tree): Unit = tree match
          case tree: TermReferenceTree =>
            super.traverse(tree)
            testSelect(tree)
          case _ =>
            super.traverse(tree)
      }
    end traverser

    // Ignore LazyVals.scala because it contains references to sun.misc, which is not in java.base
    val RuntimeLazyValsClass = ctx.findTopLevelModuleClass("scala.runtime.LazyVals")

    traverseEveryTopLevelClassDef(_ != RuntimeLazyValsClass)(traverser)

    tracker.finalize(
      // As of this writing, there were 15293 successes
      minExpectedSuccessCount = 15000,
      errorTitle = "Could not resolve the `symbol` of some trees on the classpath:"
    )
  }

  testWithContext("all-tree-types") {
    /* Test that we can compute the `.tpe` of all the `TermTree`s
     * within the test-sources and standard library.
     */

    val tracker = new Tracker

    val traverser =
      new TreeTraverser {
        override def traverse(tree: Tree): Unit =
          super.traverse(tree)
          tree match
            case tree: TermTree =>
              try
                tree.tpe
                tracker.registerSuccess()
              catch
                case ex: InvalidProgramStructureException =>
                  tracker.addError(ex)
            case _ =>
              ()
      }
    end traverser

    // Ignore LazyVals.scala because it contains references to sun.misc, which is not in java.base
    val RuntimeLazyValsClass = ctx.findTopLevelModuleClass("scala.runtime.LazyVals")

    traverseEveryTopLevelClassDef(_ != RuntimeLazyValsClass)(traverser)

    tracker.finalize(
      // As of this writing, there were 44959 successes
      minExpectedSuccessCount = 44000,
      errorTitle = "Could not compute the `tpe` of some term trees on the classpath:"
    )
  }

end WholeClasspathSuite

object WholeClasspathSuite:
  import munit.Assertions.*

  final class Tracker:
    private var successCount: Int = 0
    private val errorsBuilder = List.newBuilder[String]

    def registerSuccess(): Unit =
      successCount += 1

    def addError(message: String): Unit =
      errorsBuilder += message

    def addError(exception: Throwable): Unit =
      addError(exception.toString())

    def finalize(minExpectedSuccessCount: Int, errorTitle: String)(using munit.Location): Unit =
      val errors = errorsBuilder.result()
      if errors.nonEmpty then fail(errors.mkString(errorTitle + "\n", "\n", "\n"))

      assert(clue(successCount) >= clue(minExpectedSuccessCount))
    end finalize
  end Tracker
end WholeClasspathSuite
