import tastyquery.Contexts
import tastyquery.Contexts.FileContext
import tastyquery.ast.Names.{EmptyPackageName, Name, SimpleName, TypeName}
import tastyquery.ast.Symbols.{DeclaringSymbol, PackageClassSymbol, Symbol}

class SymbolSuite extends BaseUnpicklingSuite {
  type DeclarationPath = List[Name]

  extension (path: DeclarationPath) def toDebugString: String = path.map(_.toDebugString).mkString(".")

  extension (symbols: Iterable[Name]) def toDebugString: String = s"[${symbols.map(_.toDebugString).mkString(", ")}]"

  def getUnpicklingContext(filename: String): FileContext = {
    val ctx = Contexts.empty(filename)
    unpickle(filename)(using ctx)
    ctx
  }

  private def followPath(root: Symbol, path: DeclarationPath): Symbol = path match {
    case Nil => root
    case next :: rest =>
      assert(
        clue(root).isInstanceOf[DeclaringSymbol],
        s"Unexpected non-declaring symbol ${root.toDebugString} on the declaration path ${path.toDebugString}"
      )
      val nextDecl = root.asInstanceOf[DeclaringSymbol].getDecl(next)
      assert(nextDecl.nonEmpty, s"No declaration for ${next.toDebugString} in ${root.toDebugString}")
      val res = followPath(nextDecl.get, rest)
      res
  }

  def assertContainsDeclaration(ctx: FileContext, path: DeclarationPath): Unit =
    followPath(ctx.defn.RootPackage, path)

  def getDeclsByPrefix(ctx: FileContext, prefix: DeclarationPath): Seq[Symbol] = {
    def symbolsInSubtree(root: Symbol): Seq[Symbol] =
      if (root.isInstanceOf[DeclaringSymbol]) {
        root +: root.asInstanceOf[DeclaringSymbol].declarations.toSeq.flatMap(symbolsInSubtree(_))
      } else {
        Seq(root)
      }
    symbolsInSubtree(followPath(ctx.defn.RootPackage, prefix))
  }

  def assertForallWithPrefix(ctx: FileContext, prefix: DeclarationPath, condition: Symbol => Boolean): Unit =
    assert(
      getDeclsByPrefix(ctx, prefix).forall(condition),
      s"Condition does not hold for ${getDeclsByPrefix(ctx, prefix).filter(!condition(_))}"
    )

  def assertContainsExactly(ctx: FileContext, prefix: DeclarationPath, symbolNames: Set[Name]): Unit = {
    val decls = getDeclsByPrefix(ctx, prefix).map(_.name)
    // each declaration is in the passed set
    assert(
      decls.forall(symbolNames.contains(_)),
      s"Unexpected declarations: ${decls.filter(!symbolNames.contains(_)).toDebugString}"
    )
    // every name in the passed set is a declaration
    assert(
      symbolNames.forall(decls.contains(_)),
      s"Declaration not found: ${symbolNames.filter(!decls.contains(_)).toDebugString}"
    )
  }

  test("basic-symbol-structure") {
    val ctx = getUnpicklingContext("empty_class/EmptyClass")
    assertContainsDeclaration(ctx, SimpleName("empty_class") :: TypeName(SimpleName("EmptyClass")) :: Nil)
    // EmptyClass and its constructor are the only declarations in empty_class package
    assertContainsExactly(
      ctx,
      SimpleName("empty_class") :: Nil,
      Set(SimpleName("empty_class"), TypeName(SimpleName("EmptyClass")), SimpleName("<init>"))
    )
  }

  test("inner-class") {
    val ctx = getUnpicklingContext("simple_trees/InnerClass")
    // Inner is a declaration in InnerClass
    assertContainsDeclaration(
      ctx,
      SimpleName("simple_trees") :: TypeName(SimpleName("InnerClass")) :: TypeName(SimpleName("Inner")) :: Nil
    )
  }

  test("empty-package-contains-no-packages") {
    val ctx = getUnpicklingContext("simple_trees/SharedPackageReference$package")
    // simple_trees is not a subpackage of empty package
    assertForallWithPrefix(
      ctx,
      EmptyPackageName :: Nil,
      s => s.name == EmptyPackageName || !s.isInstanceOf[PackageClassSymbol]
    )
  }

  test("class-parameter-is-a-decl") {
    val ctx = getUnpicklingContext("simple_trees/ConstructorWithParameters")
    assertContainsExactly(
      ctx,
      SimpleName("simple_trees") :: TypeName(SimpleName("ConstructorWithParameters")) :: Nil,
      Set(
        TypeName(SimpleName("ConstructorWithParameters")),
        SimpleName("<init>"),
        SimpleName("local"),
        SimpleName("theVal"),
        SimpleName("privateVal"),
        // var and the setter for it
        SimpleName("theVar"),
        SimpleName("theVar_=")
      )
    )
  }

  test("class-type-parameter-is-not-a-decl") {
    val ctx = getUnpicklingContext("simple_trees/GenericClass")
    assertContainsExactly(
      ctx,
      SimpleName("simple_trees") :: Nil,
      Set(SimpleName("simple_trees"), TypeName(SimpleName("GenericClass")), SimpleName("<init>"))
    )
  }

  test("method-parameter-is-not-a-decl") {
    val ctx = getUnpicklingContext("simple_trees/GenericMethod")
    assertContainsExactly(
      ctx,
      SimpleName("simple_trees") :: TypeName(SimpleName("GenericMethod")) :: SimpleName("usesTypeParam") :: Nil,
      Set(SimpleName("usesTypeParam"))
    )
  }

  test("nested-method-is-not-a-decl") {
    val ctx = getUnpicklingContext("simple_trees/NestedMethod")
    assertContainsExactly(
      ctx,
      SimpleName("simple_trees") :: TypeName(SimpleName("NestedMethod")) :: SimpleName("outerMethod") :: Nil,
      // innerMethod is not a declaration of outerMethod
      Set(SimpleName("outerMethod"))
    )
  }
}
