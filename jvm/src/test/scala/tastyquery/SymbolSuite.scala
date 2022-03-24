package tastyquery

import tastyquery.Contexts.{BaseContext, baseCtx}
import tastyquery.ast.Names.{nme, Name, SimpleName, TypeName}
import tastyquery.ast.Symbols.{DeclaringSymbol, PackageClassSymbol, Symbol}
import tastyquery.ast.Symbols.ClassSymbol

class SymbolSuite extends BaseUnpicklingSuite(withClasses = false, withStdLib = false, allowDeps = false) {
  import BaseUnpicklingSuite.Decls.*
  import BaseUnpicklingSuite.toDebugString

  val empty_class = name"empty_class".singleton
  val simple_trees = name"simple_trees".singleton
  val `simple_trees.nested` = simple_trees / name"nested"

  def getDeclsByPrefix(prefix: DeclarationPath)(using BaseContext): Seq[Symbol] = {
    def symbolsInSubtree(root: Symbol): Seq[Symbol] =
      if (root.isInstanceOf[DeclaringSymbol]) {
        root +: root.asInstanceOf[DeclaringSymbol].declarations.toSeq.flatMap(symbolsInSubtree(_))
      } else {
        Seq(root)
      }
    symbolsInSubtree(resolve(prefix)).tail // discard prefix
  }

  def assertForallWithPrefix(prefix: DeclarationPath, condition: Symbol => Boolean)(using BaseContext): Unit =
    assert(
      getDeclsByPrefix(prefix).forall(condition),
      s"Condition does not hold for ${getDeclsByPrefix(prefix).filter(!condition(_))}"
    )

  def assertContainsExactly(prefix: DeclarationPath, symbolPaths: Set[DeclarationPath])(using BaseContext): Unit = {
    val decls = getDeclsByPrefix(prefix)
    val expected = symbolPaths.toList.map(p => resolve(p))
    // each declaration is in the passed set
    assert(
      decls.forall(decls.contains(_)),
      s"Unexpected declarations: ${decls.filter(!expected.contains(_)).map(_.name).toDebugString}"
    )
    // every name in the passed set is a declaration
    assert(
      expected.forall(decls.contains(_)),
      s"Declaration not found: ${expected.filter(!decls.contains(_)).map(_.name).toDebugString}"
    )
  }

  test("basic-symbol-structure") {
    val EmptyClass = empty_class / tname"EmptyClass"
    given BaseContext = getUnpicklingContext(EmptyClass)
    resolve(EmptyClass)
    // EmptyClass and its constructor are the only declarations in empty_class package
    assertContainsExactly(
      empty_class,
      Set(empty_class / tname"EmptyClass", empty_class / tname"EmptyClass" / name"<init>")
    )
  }

  test("basic-symbol-structure-nested") {
    val InNestedPackage = `simple_trees.nested` / tname"InNestedPackage"
    given BaseContext = getUnpicklingContext(InNestedPackage)
    resolve(InNestedPackage)
    // EmptyClass and its constructor are the only declarations in empty_class package
    assertContainsExactly(
      `simple_trees.nested`,
      Set(`simple_trees.nested` / tname"InNestedPackage", `simple_trees.nested` / tname"InNestedPackage" / name"<init>")
    )
  }

  test("inner-class") {
    val InnerClass = simple_trees / tname"InnerClass"
    given BaseContext = getUnpicklingContext(InnerClass)
    // Inner is a declaration in InnerClass
    resolve(InnerClass / tname"Inner")
  }

  test("empty-package-contains-no-packages") {
    given BaseContext = getUnpicklingContext(simple_trees / tname"SharedPackageReference$$package")
    // simple_trees is not a subpackage of empty package
    assertForallWithPrefix(
      nme.EmptyPackageName.singleton,
      s => s.name == nme.EmptyPackageName || !s.isInstanceOf[PackageClassSymbol]
    )
  }

  test("class-parameter-is-a-decl") {
    val ConstructorWithParameters = simple_trees / tname"ConstructorWithParameters"
    given BaseContext = getUnpicklingContext(ConstructorWithParameters)
    assertContainsExactly(
      ConstructorWithParameters,
      Set(
        ConstructorWithParameters / name"<init>",
        ConstructorWithParameters / name"local",
        ConstructorWithParameters / name"theVal",
        ConstructorWithParameters / name"privateVal",
        // var and the setter for it
        ConstructorWithParameters / name"theVar",
        ConstructorWithParameters / name"theVar_="
      )
    )
  }

  test("class-type-parameter-is-not-a-decl") {
    val GenericClass = simple_trees / tname"GenericClass"
    given BaseContext = getUnpicklingContext(GenericClass)
    assertContainsExactly(simple_trees, Set(GenericClass, GenericClass / name"<init>"))
  }

  test("method-type-parameter-is-not-a-decl") {
    val GenericMethod = simple_trees / tname"GenericMethod"
    given BaseContext = getUnpicklingContext(GenericMethod)
    assertContainsExactly(
      GenericMethod / name"usesTypeParam",
      // No declaratiins as type parameter `T` is not a declaration of `usesTypeParam`
      Set.empty
    )
  }

  test("method-term-parameter-is-not-a-decl") {
    val GenericMethod = simple_trees / tname"GenericMethod"
    given BaseContext = getUnpicklingContext(GenericMethod)
    assertContainsExactly(
      GenericMethod / name"usesTermParam",
      // No declaratiins as term parameter `i: Int` is not a declaration of `usesTermParam`
      Set.empty
    )
  }

  test("nested-method-is-not-a-decl") {
    val NestedMethod = simple_trees / tname"NestedMethod"
    given BaseContext = getUnpicklingContext(NestedMethod)
    assertContainsExactly(
      NestedMethod / name"outerMethod",
      // local method `innerMethod` is not a declaration of `outerMethod`
      Set.empty
    )
  }

  test("sibling-top-level-class-loading") {
    val Constants = simple_trees / tname"Constants"
    val NestedMethod = simple_trees / tname"NestedMethod"
    val outerMethod = NestedMethod / name"outerMethod"
    val unitVal = Constants / name"unitVal"

    given BaseContext = getUnpicklingContext(Constants, extraClasspath = NestedMethod)

    assertSymbolExistsAndIsLoaded(Constants) // we should have loaded Constants, we requested it
    assertSymbolExistsAndIsLoaded(unitVal) // outerMethod is a member of Constants, it should be seen.

    assertSymbolExistsAndIsLoaded(NestedMethod) // sibling top-level class is also seen in same package
    assertSymbolNotExistsOrNotLoadedYet(outerMethod) // members of sibling top-level class are not seen unless requested
  }

  test("demo-symbolic-package-leaks".ignore) {
    // ignore because this passes only on clean builds

    def failingGetTopLevelClass(path: TopLevelDeclPath)(using BaseContext): Nothing =
      baseCtx.getClassIfDefined(path.fullClassName) match
        case Some(classRoot) => fail(s"expected no class, but got $classRoot")
        case _               => throw MissingTopLevelDecl(path)

    def forceTopLevel(path: TopLevelDeclPath)(using BaseContext): Unit = {
      val classRoot = baseCtx.getClassIfDefined(path.fullClassName) match
        case Some(cls) => cls
        case _         => throw MissingTopLevelDecl(path)
      try
        baseCtx.classloader.scanClass(classRoot)
        fail(s"expected failure when scanning class ${path.fullClassName}, $classRoot")
      catch
        case err: java.lang.AssertionError =>
          val msg = err.getMessage.nn
          assert(
            msg.contains("unexpected package symbolic_>> in owners of top level class symbolic_$greater$greater.#::")
          )
    }

    def runTest(using BaseContext): Unit =
      val `symbolic_>>.#::` = name"symbolic_>>" / tname"#::"
      val `symbolic_$greater$greater.#::` = name"symbolic_$$greater$$greater" / tname"#::"

      intercept[MissingTopLevelDecl] {
        failingGetTopLevelClass(`symbolic_>>.#::`) // this will fail, we can't find a symbolic package
      }
      assertSymbolNotExistsOrNotLoadedYet(`symbolic_>>.#::`) // still does not exist
      assertSymbolNotExistsOrNotLoadedYet(`symbolic_$greater$greater.#::`) // not existant yet

      // we will read the TASTy file of this class, causing an assertion error when we read the symbolic
      // package in tasty - the owners of the classroot do not match
      forceTopLevel(`symbolic_$greater$greater.#::`)

    runTest(using Contexts.init(testClasspath))
  }
}
