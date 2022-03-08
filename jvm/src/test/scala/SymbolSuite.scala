import tastyquery.Contexts
import tastyquery.Contexts.FileContext
import tastyquery.ast.Names.{nme, Name, SimpleName, TypeName}
import tastyquery.ast.Symbols.{DeclaringSymbol, PackageClassSymbol, Symbol}

class SymbolSuite extends BaseUnpicklingSuite(withClasses = false, withStdLib = false) {
  import BaseUnpicklingSuite.Decls.*
  import BaseUnpicklingSuite.toDebugString

  val empty_class = name"empty_class".singleton
  val simple_trees = name"simple_trees".singleton
  val `simple_trees.nested` = simple_trees / name"nested"

  def getUnpicklingContext(path: TopLevelDeclPath): FileContext =
    unpickleCtx(path)

  def assertContainsDeclaration(ctx: FileContext, path: DeclarationPath): Unit =
    resolve(path)(using ctx)

  def assertMissingDeclaration(ctx: FileContext, path: DeclarationPath): Unit =
    absent(path)(using ctx)

  def getDeclsByPrefix(ctx: FileContext, prefix: DeclarationPath): Seq[Symbol] = {
    def symbolsInSubtree(root: Symbol): Seq[Symbol] =
      if (root.isInstanceOf[DeclaringSymbol]) {
        root +: root.asInstanceOf[DeclaringSymbol].declarations.toSeq.flatMap(symbolsInSubtree(_))
      } else {
        Seq(root)
      }
    symbolsInSubtree(followPath(ctx.defn.RootPackage, prefix)).tail // discard prefix
  }

  def assertForallWithPrefix(ctx: FileContext, prefix: DeclarationPath, condition: Symbol => Boolean): Unit =
    assert(
      getDeclsByPrefix(ctx, prefix).forall(condition),
      s"Condition does not hold for ${getDeclsByPrefix(ctx, prefix).filter(!condition(_))}"
    )

  def assertContainsExactly(ctx: FileContext, prefix: DeclarationPath, symbolPaths: Set[DeclarationPath]): Unit = {
    val decls = getDeclsByPrefix(ctx, prefix)
    val expected = symbolPaths.toList.map(p => resolve(p)(using ctx))
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
    val ctx = getUnpicklingContext(EmptyClass)
    assertContainsDeclaration(ctx, EmptyClass)
    // EmptyClass and its constructor are the only declarations in empty_class package
    assertContainsExactly(
      ctx,
      empty_class,
      Set(empty_class / tname"EmptyClass", empty_class / tname"EmptyClass" / name"<init>")
    )
  }

  test("fail-on-symbolic-package:it-should-be-missing") {
    intercept[MissingTopLevelDecl] {
      getUnpicklingContext(name"symbolic_>>" / tname"#::") // this will fail, we can't find a symbolic package
    }
    val ctx = getUnpicklingContext(name"symbolic_$$greater$$greater" / tname"#::") // can only find encoded version
  }

  test("basic-symbol-structure-nested") {
    val InNestedPackage = `simple_trees.nested` / tname"InNestedPackage"
    val ctx = getUnpicklingContext(InNestedPackage)
    assertContainsDeclaration(ctx, InNestedPackage)
    // EmptyClass and its constructor are the only declarations in empty_class package
    assertContainsExactly(
      ctx,
      `simple_trees.nested`,
      Set(`simple_trees.nested` / tname"InNestedPackage", `simple_trees.nested` / tname"InNestedPackage" / name"<init>")
    )
  }

  test("inner-class") {
    val InnerClass = simple_trees / tname"InnerClass"
    val ctx = getUnpicklingContext(InnerClass)
    // Inner is a declaration in InnerClass
    assertContainsDeclaration(ctx, InnerClass / tname"Inner")
  }

  test("empty-package-contains-no-packages") {
    val ctx = getUnpicklingContext(simple_trees / tname"SharedPackageReference$$package")
    // simple_trees is not a subpackage of empty package
    assertForallWithPrefix(
      ctx,
      nme.EmptyPackageName.singleton,
      s => s.name == nme.EmptyPackageName || !s.isInstanceOf[PackageClassSymbol]
    )
  }

  test("class-parameter-is-a-decl") {
    val ConstructorWithParameters = simple_trees / tname"ConstructorWithParameters"
    val ctx = getUnpicklingContext(ConstructorWithParameters)
    assertContainsExactly(
      ctx,
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
    val ctx = getUnpicklingContext(GenericClass)
    assertContainsExactly(ctx, simple_trees, Set(GenericClass, GenericClass / name"<init>"))
  }

  test("method-type-parameter-is-not-a-decl") {
    val GenericMethod = simple_trees / tname"GenericMethod"
    val ctx = getUnpicklingContext(GenericMethod)
    assertContainsExactly(
      ctx,
      GenericMethod / name"usesTypeParam",
      // No declaratiins as type parameter `T` is not a declaration of `usesTypeParam`
      Set.empty
    )
  }

  test("method-term-parameter-is-not-a-decl") {
    val GenericMethod = simple_trees / tname"GenericMethod"
    val ctx = getUnpicklingContext(GenericMethod)
    assertContainsExactly(
      ctx,
      GenericMethod / name"usesTermParam",
      // No declaratiins as term parameter `i: Int` is not a declaration of `usesTermParam`
      Set.empty
    )
  }

  test("nested-method-is-not-a-decl") {
    val NestedMethod = simple_trees / tname"NestedMethod"
    val ctx = getUnpicklingContext(NestedMethod)
    assertContainsExactly(
      ctx,
      NestedMethod / name"outerMethod",
      // local method `innerMethod` is not a declaration of `outerMethod`
      Set.empty
    )
  }

  test("laziness-of-package-loading") {
    val Constants = simple_trees / tname"Constants"
    val NestedMethod = simple_trees / tname"NestedMethod"
    val ctx = getUnpicklingContext(Constants)
    assertContainsDeclaration(ctx, Constants)

    // `NestedMethod` is in same package, but unforced as TASTy is not scanned
    assertMissingDeclaration(ctx, NestedMethod)
  }
}
