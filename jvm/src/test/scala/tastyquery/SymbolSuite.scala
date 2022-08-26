package tastyquery

import tastyquery.Contexts.Context
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*

import Paths.*

class SymbolSuite extends RestrictedUnpicklingSuite {
  val empty_class = name"empty_class".singleton
  val simple_trees = name"simple_trees".singleton
  val `simple_trees.nested` = simple_trees / name"nested"

  def getDeclsByPrefix(prefix: DeclarationPath)(using Context): Seq[Symbol] = {
    def symbolsInSubtree(root: Symbol): Seq[Symbol] =
      if (root.isInstanceOf[DeclaringSymbol]) {
        root +: root.asInstanceOf[DeclaringSymbol].declarations.toSeq.flatMap(symbolsInSubtree(_))
      } else {
        Seq(root)
      }
    symbolsInSubtree(resolve(prefix)).tail // discard prefix
  }

  def assertForallWithPrefix(prefix: DeclarationPath, condition: Symbol => Boolean)(using Context): Unit =
    assert(
      getDeclsByPrefix(prefix).forall(condition),
      s"Condition does not hold for ${getDeclsByPrefix(prefix).filter(!condition(_))}"
    )

  def assertContainsExactly(prefix: DeclarationPath, symbolPaths: Set[DeclarationPath])(using Context): Unit = {
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
    given Context = getUnpicklingContext(EmptyClass)
    resolve(EmptyClass)
    // EmptyClass and its constructor are the only declarations in empty_class package
    assertContainsExactly(
      empty_class,
      Set(empty_class / tname"EmptyClass", empty_class / tname"EmptyClass" / name"<init>")
    )
  }

  test("basic-symbol-structure-nested") {
    val InNestedPackage = `simple_trees.nested` / tname"InNestedPackage"
    given Context = getUnpicklingContext(InNestedPackage)
    resolve(InNestedPackage)
    // EmptyClass and its constructor are the only declarations in empty_class package
    assertContainsExactly(
      `simple_trees.nested`,
      Set(`simple_trees.nested` / tname"InNestedPackage", `simple_trees.nested` / tname"InNestedPackage" / name"<init>")
    )
  }

  test("inner-class") {
    val InnerClass = simple_trees / tname"InnerClass"
    given Context = getUnpicklingContext(InnerClass)
    // Inner is a declaration in InnerClass
    resolve(InnerClass / tname"Inner")
  }

  test("empty-package-contains-no-packages") {
    given Context = getUnpicklingContext(simple_trees / tname"SharedPackageReference$$package")
    // simple_trees is not a subpackage of empty package
    assertForallWithPrefix(
      nme.EmptyPackageName.singleton,
      s => s.name == nme.EmptyPackageName || !s.isInstanceOf[PackageClassSymbol]
    )
  }

  test("class-parameter-is-a-decl") {
    val ConstructorWithParameters = simple_trees / tname"ConstructorWithParameters"
    given Context = getUnpicklingContext(ConstructorWithParameters)
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
    given Context = getUnpicklingContext(GenericClass)
    assertContainsExactly(simple_trees, Set(GenericClass, GenericClass / name"<init>"))
  }

  test("method-type-parameter-is-not-a-decl") {
    val GenericMethod = simple_trees / tname"GenericMethod"
    given Context = getUnpicklingContext(GenericMethod)
    assertContainsExactly(
      GenericMethod / name"usesTypeParam",
      // No declaratiins as type parameter `T` is not a declaration of `usesTypeParam`
      Set.empty
    )
  }

  test("method-term-parameter-is-not-a-decl") {
    val GenericMethod = simple_trees / tname"GenericMethod"
    given Context = getUnpicklingContext(GenericMethod)
    assertContainsExactly(
      GenericMethod / name"usesTermParam",
      // No declaratiins as term parameter `i: Int` is not a declaration of `usesTermParam`
      Set.empty
    )
  }

  test("nested-method-is-not-a-decl") {
    val NestedMethod = simple_trees / tname"NestedMethod"
    given Context = getUnpicklingContext(NestedMethod)
    assertContainsExactly(
      NestedMethod / name"outerMethod",
      // local method `innerMethod` is not a declaration of `outerMethod`
      Set.empty
    )
  }

  test("nested-package-lookup") {
    import tastyquery.ast.Types.*

    val InNestedPackage = `simple_trees.nested` / tname"InNestedPackage"
    given Context = getUnpicklingContext(InNestedPackage)

    assert(resolve(InNestedPackage).fullName.toString == "simple_trees.nested.InNestedPackage")

    val (simpleTreesPkg @ _: PackageClassSymbol) = resolve(simple_trees): @unchecked

    assert(simpleTreesPkg.fullName.toString == "simple_trees")

    val (simpleTreesNestedPkg @ _: PackageClassSymbol) = simpleTreesPkg.getDecl(name"nested").get: @unchecked

    assert(simpleTreesNestedPkg.fullName.toString == "simple_trees.nested")

    assert(TermRef(PackageRef(simpleTreesPkg), name"nested").symbol == simpleTreesNestedPkg)
  }
}
