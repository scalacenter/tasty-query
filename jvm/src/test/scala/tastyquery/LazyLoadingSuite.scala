package tastyquery

import tastyquery.Contexts.*
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*

import BaseUnpicklingSuite.Decls.*
import RestrictedUnpicklingSuite.MissingTopLevelDecl

/** The lazy-loading suite explicitly tests that some operations do, and do
  * not, trigger loading of particular information.
  *
  * These tests intentionally break the auto-loading semantics of the API,
  * through access to `private[tastyquery]` methods.
  */
class LazyLoadingSuite extends RestrictedUnpicklingSuite {
  val simple_trees = name"simple_trees".singleton

  /** Dangerous operations that break auto-loading semantics of the API.
    *
    * They can only do that because they access `private[tastyquery]` methods,
    * in particular `Symbol.getDeclInternal`.
    */
  object DangerousOps {
    def followPathImpl(root: DeclaringSymbol, path: DeclarationPath): Either[String, Symbol] = {
      def follow(selected: Symbol)(remainder: DeclarationPath): Either[String, Symbol] = selected match {
        case nextDecl: DeclaringSymbol =>
          followPathImpl(nextDecl, remainder)
        case someSym =>
          val symDebug = clue(someSym).toDebugString
          Left(s"Unexpected non-declaring symbol $symDebug with remaining path ${remainder.debug}")
      }
      for
        selected <- select(root, path.root)
        sym <- path.foldRemainder(Right(selected))(follow(selected))
      yield sym
    }

    private def select(root: DeclaringSymbol, next: Name): Either[String, Symbol] = {
      val sel = (root, next) match {
        case (p: PackageClassSymbol, s: SimpleName) if p.name != nme.RootName =>
          p.name.toTermName.select(s)
        case _ => next
      }
      root.getDeclInternal(sel) match {
        case Some(someSym) => Right(someSym)
        case _ => Left(s"No declaration for ${next.toDebugString} [${sel.toDebugString}] in ${root.toDebugString}")
      }
    }
  }

  def assertSymbolExistsAndIsLoaded(path: DeclarationPath)(implicit ctx: BaseContext): Unit =
    DangerousOps.followPathImpl(defn.RootPackage, path).fold(fail(_), _ => ())

  def assertSymbolNotExistsOrNotLoadedYet(path: DeclarationPath)(implicit ctx: BaseContext): Unit =
    def unexpected(sym: Symbol) = fail(s"expected no symbol, but found ${sym.toDebugString}")
    DangerousOps.followPathImpl(defn.RootPackage, path).fold(_ => (), unexpected)

  /** Explicitly initializes any symbol. */
  def explicitlyInitialize(sym: Symbol)(using BaseContext): Unit =
    sym match
      case sym: DeclaringSymbol => sym.declarations // trigger the initialization
      case _                    => () // already initialized, by construction

  test("sibling-top-level-class-loading") {
    val Constants = simple_trees / tname"Constants"
    val NestedMethod = simple_trees / tname"NestedMethod"
    val outerMethod = NestedMethod / name"outerMethod"
    val unitVal = Constants / name"unitVal"

    given BaseContext = getUnpicklingContext(Constants, extraClasspath = NestedMethod)

    explicitlyInitialize(resolve(Constants))

    assertSymbolExistsAndIsLoaded(Constants) // we should have loaded Constants, we requested it
    assertSymbolExistsAndIsLoaded(unitVal) // outerMethod is a member of Constants, it should be seen.

    assertSymbolExistsAndIsLoaded(NestedMethod) // sibling top-level class is also seen in same package
    assertSymbolNotExistsOrNotLoadedYet(outerMethod) // members of sibling top-level class are not seen unless requested
  }

  test("demo-symbolic-package-leaks".ignore) {
    // ignore because this passes only on clean builds

    def failingGetTopLevelClass(path: TopLevelDeclPath)(using BaseContext): Nothing =
      baseCtx.getClassIfDefined(path.fullClassName) match
        case Right(classRoot) => fail(s"expected no class, but got $classRoot")
        case Left(err)        => throw MissingTopLevelDecl(path, err)

    def forceTopLevel(path: TopLevelDeclPath)(using BaseContext): Unit = {
      val classRoot = baseCtx.getClassIfDefined(path.fullClassName) match
        case Right(cls) => cls
        case Left(err)  => throw MissingTopLevelDecl(path, err)
      try
        baseCtx.classloader.scanClass(classRoot)
        fail(s"expected failure when scanning class ${path.fullClassName}, $classRoot")
      catch
        case err: java.lang.AssertionError =>
          val msg = err.getMessage.nn
          assert(
            msg.contains("unexpected package symbolic_-- in owners of top level class symbolic_$minus$minus.#::")
          )
    }

    def runTest(using BaseContext): Unit =
      val `symbolic_--.#::` = name"symbolic_--" / tname"#::"
      val `symbolic_$minus$minus.#::` = name"symbolic_$$minus$$minus" / tname"#::"

      intercept[MissingTopLevelDecl] {
        failingGetTopLevelClass(`symbolic_--.#::`) // this will fail, we can't find a symbolic package
      }
      assertSymbolNotExistsOrNotLoadedYet(`symbolic_--.#::`) // still does not exist
      assertSymbolNotExistsOrNotLoadedYet(`symbolic_$minus$minus.#::`) // not existant yet

      // we will read the TASTy file of this class, causing an assertion error when we read the symbolic
      // package in tasty - the owners of the classroot do not match
      forceTopLevel(`symbolic_$minus$minus.#::`)

    runTest(using Contexts.init(testClasspath))
  }
}
