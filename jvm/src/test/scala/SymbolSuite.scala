import tastyquery.Contexts
import tastyquery.Contexts.Context
import tastyquery.ast.Names.{EmptyPackageName, Name, SimpleName, TypeName}
import tastyquery.ast.Symbols.{DeclaringSymbol, PackageClassSymbol, Symbol}

class SymbolSuite extends BaseUnpicklingSuite {
  type DeclarationPath = List[Name]

  extension (path: DeclarationPath)
    def toDebugString: String = path.map(_.toDebugString).mkString(".")

  extension (symbols: Iterable[Name])
    def toDebugString: String = s"[${symbols.map(_.toDebugString).mkString(", ")}]"

  def getUnpicklingContext(filename: String): Context = {
    val ctx = Contexts.empty
    unpickle(filename) (using ctx)
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

  def assertContainsDeclaration(ctx: Context, path: DeclarationPath): Unit =
    followPath(ctx.defn.RootPackage, path)

  def getDeclsByPrefix(ctx: Context, prefix: DeclarationPath): List[Symbol] = {
    def symbolsInSubtree(root: Symbol): List[Symbol] =
      if (root.isInstanceOf[DeclaringSymbol]) {
        root :: root.asInstanceOf[DeclaringSymbol].declarations.flatMap(symbolsInSubtree(_))
      } else {
        root :: Nil
      }
    symbolsInSubtree(followPath(ctx.defn.RootPackage, prefix))
  }

  def assertForallWithPrefix(ctx: Context, prefix: DeclarationPath, condition: Symbol => Boolean): Unit =
    assert(
      getDeclsByPrefix(ctx, prefix).forall(condition),
      s"Condition does not hold for ${getDeclsByPrefix(ctx, prefix).filter(!condition(_))}"
    )

  def assertContainsOnly(ctx: Context, prefix: DeclarationPath, symbolNames: Set[Name]): Unit =
    assertForallWithPrefix(ctx, prefix, s => symbolNames.contains(s.name))

  test("basic-symbol-structure") {
    val ctx = getUnpicklingContext("empty_class/EmptyClass")
    assertContainsDeclaration(ctx, SimpleName("empty_class") :: TypeName(SimpleName("EmptyClass")) :: Nil)
    // EmptyClass and its constructor are the only declarations in empty_class package
    assertContainsOnly(
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
    assertForallWithPrefix(ctx, EmptyPackageName :: Nil, s => s.name == EmptyPackageName || !s.isInstanceOf[PackageClassSymbol])
  }
}
