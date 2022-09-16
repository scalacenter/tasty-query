package tastyquery

import scala.concurrent.ExecutionContext.Implicits.global

import tastyquery.Contexts.Context
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*

import Paths.*
import tastyquery.ast.Trees.{ClassDef, ValDef}

class SymbolSuite extends RestrictedUnpicklingSuite {
  val empty_class = RootPkg / name"empty_class"
  val simple_trees = RootPkg / name"simple_trees"
  val inheritance = RootPkg / name"inheritance"
  val `simple_trees.nested` = simple_trees / name"nested"

  def testWithContext(name: String, path: TopLevelDeclPath)(using munit.Location)(body: Context ?=> Unit): Unit =
    testWithContext(new munit.TestOptions(name), path)(body)

  def testWithContext(options: munit.TestOptions, path: TopLevelDeclPath)(
    using munit.Location
  )(body: Context ?=> Unit): Unit =
    test(options) {
      for ctx <- getUnpicklingContext(path) yield body(using ctx)
    }

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

  testWithContext(
    "top-level-package-object[class]-empty-package",
    EmptyPkg / tname"toplevelEmptyPackage$$package" / obj
  ) {
    val toplevelEmptyPackage_package = EmptyPkg / tname"toplevelEmptyPackage$$package" / obj

    val toplevelEmptyPackage_packageClass = resolve(toplevelEmptyPackage_package)

    val (tree @ _: ClassDef) = toplevelEmptyPackage_packageClass.tree.get: @unchecked

    assert(tree.name == toplevelEmptyPackage_package.name)
    assert(tree.symbol == toplevelEmptyPackage_packageClass)
  }

  testWithContext(
    "top-level-package-object[value]-empty-package",
    EmptyPkg / name"toplevelEmptyPackage$$package" / obj
  ) {
    val toplevelEmptyPackage_package = EmptyPkg / name"toplevelEmptyPackage$$package" / obj

    val toplevelEmptyPackage_packageValue = resolve(toplevelEmptyPackage_package)

    val (tree @ _: ValDef) = toplevelEmptyPackage_packageValue.tree.get: @unchecked

    assert(tree.name == name"toplevelEmptyPackage$$package")
    assert(tree.symbol == toplevelEmptyPackage_packageValue)
  }

  testWithContext(
    "top-level-package-object[companion class]-empty-package",
    EmptyPkg / name"toplevelEmptyPackage$$package" / obj
  ) {
    val toplevelEmptyPackage_package_companion = EmptyPkg / tname"toplevelEmptyPackage$$package"

    try
      resolve(toplevelEmptyPackage_package_companion)
      fail(s"Expected not to resolve class ${toplevelEmptyPackage_package_companion.rootClassName}")
    catch
      case ex: IllegalArgumentException =>
        assert(ex.getMessage.nn.contains(s"cannot find member ${tname"toplevelEmptyPackage$$package".toDebugString}"))
  }

  testWithContext("basic-symbol-structure", empty_class / tname"EmptyClass") {
    val EmptyClass = empty_class / tname"EmptyClass"
    resolve(EmptyClass)
    // EmptyClass and its constructor are the only declarations in empty_class package
    assertContainsExactly(
      empty_class,
      Set(empty_class / tname"EmptyClass", empty_class / tname"EmptyClass" / name"<init>")
    )
  }

  testWithContext("basic-symbol-structure-nested", `simple_trees.nested` / tname"InNestedPackage") {
    val InNestedPackage = `simple_trees.nested` / tname"InNestedPackage"
    resolve(InNestedPackage)
    // EmptyClass and its constructor are the only declarations in empty_class package
    assertContainsExactly(
      `simple_trees.nested`,
      Set(`simple_trees.nested` / tname"InNestedPackage", `simple_trees.nested` / tname"InNestedPackage" / name"<init>")
    )
  }

  testWithContext("inner-class", simple_trees / tname"InnerClass") {
    val InnerClass = simple_trees / tname"InnerClass"
    // Inner is a declaration in InnerClass
    resolve(InnerClass / tname"Inner")
  }

  testWithContext("empty-package-contains-no-packages", simple_trees / tname"SharedPackageReference$$package") {
    // simple_trees is not a subpackage of empty package
    assertForallWithPrefix(EmptyPkg, s => s.name == nme.EmptyPackageName || !s.isInstanceOf[PackageClassSymbol])
  }

  testWithContext("class-parameter-is-a-decl", simple_trees / tname"ConstructorWithParameters") {
    val ConstructorWithParameters = simple_trees / tname"ConstructorWithParameters"
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

  testWithContext("class-type-parameter-is-not-a-decl", simple_trees / tname"GenericClass") {
    val GenericClass = simple_trees / tname"GenericClass"
    assertContainsExactly(simple_trees, Set(GenericClass, GenericClass / name"<init>"))
  }

  testWithContext("method-type-parameter-is-not-a-decl", simple_trees / tname"GenericMethod") {
    val GenericMethod = simple_trees / tname"GenericMethod"
    assertContainsExactly(
      GenericMethod / name"usesTypeParam",
      // No declaratiins as type parameter `T` is not a declaration of `usesTypeParam`
      Set.empty
    )
  }

  testWithContext("method-term-parameter-is-not-a-decl", simple_trees / tname"GenericMethod") {
    val GenericMethod = simple_trees / tname"GenericMethod"
    assertContainsExactly(
      GenericMethod / name"usesTermParam",
      // No declaratiins as term parameter `i: Int` is not a declaration of `usesTermParam`
      Set.empty
    )
  }

  testWithContext("nested-method-is-not-a-decl", simple_trees / tname"NestedMethod") {
    val NestedMethod = simple_trees / tname"NestedMethod"
    assertContainsExactly(
      NestedMethod / name"outerMethod",
      // local method `innerMethod` is not a declaration of `outerMethod`
      Set.empty
    )
  }

  testWithContext("nested-package-lookup", `simple_trees.nested` / tname"InNestedPackage") {
    import tastyquery.ast.Types.*

    val InNestedPackage = `simple_trees.nested` / tname"InNestedPackage"

    assert(resolve(InNestedPackage).fullName.toString == "simple_trees.nested.InNestedPackage")

    val (simpleTreesPkg @ _: PackageClassSymbol) = resolve(simple_trees): @unchecked

    assert(simpleTreesPkg.fullName.toString == "simple_trees")

    val (simpleTreesNestedPkg @ _: PackageClassSymbol) = simpleTreesPkg.getDecl(name"nested").get: @unchecked

    assert(simpleTreesNestedPkg.fullName.toString == "simple_trees.nested")

    assert(TermRef(PackageRef(simpleTreesPkg), name"nested").symbol == simpleTreesNestedPkg)
  }

  testWithContext("basic-inheritance-same-root".ignore, inheritance / tname"SameTasty" / obj) {
    val Sub = inheritance / tname"SameTasty" / obj / tname"Sub"

    val SubClass = resolve(Sub).asClass

    val fooMethod = SubClass.ref.member(name"foo")
  }
}
