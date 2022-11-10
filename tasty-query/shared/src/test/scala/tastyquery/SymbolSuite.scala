package tastyquery

import scala.concurrent.ExecutionContext.Implicits.global

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Names.*
import tastyquery.Symbols.*

import Paths.*
import tastyquery.Trees.{ClassDef, ValDef}
import tastyquery.Types.*

class SymbolSuite extends RestrictedUnpicklingSuite {
  val empty_class = RootPkg / name"empty_class"
  val simple_trees = RootPkg / name"simple_trees"
  val `simple_trees.nested` = simple_trees / name"nested"
  val inheritance = RootPkg / name"inheritance"
  val inheritanceCrossTasty = inheritance / name"crosstasty"

  val jlObject = RootPkg / name"java" / name"lang" / tname"Object"
  val scUnit = RootPkg / name"scala" / tname"Unit"
  val scAnyVal = RootPkg / name"scala" / tname"AnyVal"

  val jlCloneable = name"java" / name"lang" / tname"Cloneable"
  val jioSerializable = name"java" / name"io" / tname"Serializable"
  val javaFunction1 = name"java" / name"util" / name"function" / tname"Function"

  /** Needed for correct resolving of ctor signatures */
  val fundamentalClasses = Seq(jlObject, scUnit, scAnyVal)

  def testWithContext(name: String, path: TopLevelDeclPath, extraClasspath: TopLevelDeclPath*)(using munit.Location)(
    body: Context ?=> Unit
  ): Unit =
    testWithContext(new munit.TestOptions(name), path, extraClasspath*)(body)

  def testWithContext(options: munit.TestOptions, path: TopLevelDeclPath, extraClasspath: TopLevelDeclPath*)(
    using munit.Location
  )(body: Context ?=> Unit): Unit =
    test(options) {
      for ctx <- getUnpicklingContext(path, extraClasspath*) yield body(using ctx)
    }

  def getDeclsByPrefix(prefix: Symbol)(using Context): Seq[Symbol] = {
    def symbolsInSubtree(root: Symbol): Seq[Symbol] =
      if (root.isInstanceOf[DeclaringSymbol]) {
        root +: root.asInstanceOf[DeclaringSymbol].declarations.toSeq.flatMap(symbolsInSubtree(_))
      } else {
        Seq(root)
      }
    symbolsInSubtree(prefix).tail // discard prefix
  }

  def assertForallWithPrefix(prefix: Symbol, condition: Symbol => Boolean)(using Context): Unit =
    assert(
      getDeclsByPrefix(prefix).forall(condition),
      s"Condition does not hold for ${getDeclsByPrefix(prefix).filter(!condition(_))}"
    )

  def assertContainsExactly(prefix: Symbol, symbolPaths: Set[DeclarationPath])(using Context): Unit = {
    val decls = getDeclsByPrefix(prefix)
    val expected = symbolPaths.toList.map(p => ctx.findSymbolFromRoot(p.toNameList))
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
    val toplevelEmptyPackage_packageClass = ctx.findTopLevelModuleClass("toplevelEmptyPackage$package")

    val (tree @ _: ClassDef) = toplevelEmptyPackage_packageClass.tree.get: @unchecked

    assert(tree.name == termName("toplevelEmptyPackage$package").withObjectSuffix.toTypeName)
    assert(tree.symbol == toplevelEmptyPackage_packageClass)
  }

  testWithContext(
    "top-level-package-object[value]-empty-package",
    EmptyPkg / name"toplevelEmptyPackage$$package" / obj
  ) {
    val toplevelEmptyPackage_packageValue = ctx.findStaticTerm("toplevelEmptyPackage$package")

    val (tree @ _: ValDef) = toplevelEmptyPackage_packageValue.tree.get: @unchecked

    assert(tree.name == termName("toplevelEmptyPackage$package"))
    assert(tree.symbol == toplevelEmptyPackage_packageValue)
  }

  testWithContext(
    "top-level-package-object[companion class]-empty-package",
    EmptyPkg / name"toplevelEmptyPackage$$package" / obj
  ) {
    try
      ctx.findStaticType("toplevelEmptyPackage$package")
      fail(s"Expected not to resolve class toplevelEmptyPackage$$package")
    catch
      case ex: MemberNotFoundException =>
        assert(ex.name == typeName("toplevelEmptyPackage$package"))
        assert(ex.prefix == defn.EmptyPackage)
  }

  testWithContext("getPackageDecl", simple_trees / tname"ScalaObject" / obj) {
    val pkg = ctx.findPackage("simple_trees")

    // Non-existent symbol
    assert(pkg.getPackageDecl(termName("nonexistentsubpackage")) == None)

    // Symbol exists but is not a package (whitebox knowledge: it is not loaded yet)
    assert(pkg.getPackageDecl(termName("ScalaObject")) == None)

    // ScalaObject actually exists as a term (but not as a package)
    assert(pkg.getDecl(name"ScalaObject").isDefined)

    // After loading ScalaObject, getPackageDecl still returns None for it
    assert(pkg.getPackageDecl(termName("ScalaObject")) == None)
  }

  testWithContext("basic-symbol-structure", empty_class / tname"EmptyClass") {
    ctx.findTopLevelClass("empty_class.EmptyClass")
    // EmptyClass and its constructor are the only declarations in empty_class package
    assertContainsExactly(
      ctx.findPackage("empty_class"),
      Set(empty_class / tname"EmptyClass", empty_class / tname"EmptyClass" / name"<init>")
    )
  }

  testWithContext("basic-symbol-structure-nested", `simple_trees.nested` / tname"InNestedPackage") {
    ctx.findTopLevelClass("simple_trees.nested.InNestedPackage")
    // EmptyClass and its constructor are the only declarations in empty_class package
    assertContainsExactly(
      ctx.findPackage("simple_trees.nested"),
      Set(`simple_trees.nested` / tname"InNestedPackage", `simple_trees.nested` / tname"InNestedPackage" / name"<init>")
    )
  }

  testWithContext("inner-class", simple_trees / tname"InnerClass") {
    val InnerClass = ctx.findTopLevelClass("simple_trees.InnerClass")
    // Inner is a declaration in InnerClass
    assert(InnerClass.getDecl(typeName("Inner")).isDefined)
  }

  testWithContext("empty-package-contains-no-packages", simple_trees / tname"SharedPackageReference$$package") {
    // simple_trees is not a subpackage of empty package
    assertForallWithPrefix(defn.EmptyPackage, s => !s.isPackage)
  }

  testWithContext("class-parameter-is-a-decl", simple_trees / tname"ConstructorWithParameters") {
    val ConstructorWithParameters = simple_trees / tname"ConstructorWithParameters"
    assertContainsExactly(
      ctx.findTopLevelClass("simple_trees.ConstructorWithParameters"),
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
    assertContainsExactly(ctx.findTopLevelClass("simple_trees.GenericClass"), Set(GenericClass / name"<init>"))
  }

  testWithContext("method-type-parameter-is-not-a-decl", simple_trees / tname"GenericMethod") {
    assertContainsExactly(
      ctx.findTopLevelClass("simple_trees.GenericMethod").findDecl(name"usesTypeParam"),
      // No declaratiins as type parameter `T` is not a declaration of `usesTypeParam`
      Set.empty
    )
  }

  testWithContext("method-term-parameter-is-not-a-decl", simple_trees / tname"GenericMethod") {
    assertContainsExactly(
      ctx.findTopLevelClass("simple_trees.GenericMethod").findDecl(name"usesTermParam"),
      // No declaratiins as term parameter `i: Int` is not a declaration of `usesTermParam`
      Set.empty
    )
  }

  testWithContext("nested-method-is-not-a-decl", simple_trees / tname"NestedMethod") {
    assertContainsExactly(
      ctx.findTopLevelClass("simple_trees.NestedMethod").findDecl(name"outerMethod"),
      // local method `innerMethod` is not a declaration of `outerMethod`
      Set.empty
    )
  }

  testWithContext("nested-package-lookup", `simple_trees.nested` / tname"InNestedPackage") {
    import tastyquery.Types.*

    val InNestedPackageClass = ctx.findTopLevelClass("simple_trees.nested.InNestedPackage")

    assert(InNestedPackageClass.fullName.toString == "simple_trees.nested.InNestedPackage")

    val simpleTreesPkg = ctx.findPackage("simple_trees")

    assert(simpleTreesPkg.fullName.toString == "simple_trees")

    val (simpleTreesNestedPkg @ _: PackageSymbol) = simpleTreesPkg.getDecl(name"nested").get: @unchecked

    assert(simpleTreesNestedPkg.fullName.toString == "simple_trees.nested")

    assert(PackageRef(simpleTreesPkg).findMember(name"nested", NoPrefix) == simpleTreesNestedPkg)
  }

  testWithContext("basic-inheritance-same-root", inheritance / tname"SameTasty" / obj, fundamentalClasses*) {
    val ParentClass = ctx.findStaticClass("inheritance.SameTasty.Parent")
    val ChildClass = ctx.findStaticClass("inheritance.SameTasty.Child")
    val SubClass = ctx.findStaticClass("inheritance.SameTasty.Sub")

    val fooMethod = SubClass.typeRef.member(name"foo")
    assert(clue(fooMethod.owner) == ChildClass)

    val getFooMethod = SubClass.typeRef.member(name"getFoo")
    assert(clue(getFooMethod.owner) == ParentClass)

    val FooTypeSym = SubClass.typeRef.member(tname"FooType")
    assert(FooTypeSym.isInstanceOf[TypeMemberSymbol])
    assert(clue(FooTypeSym.owner) == ChildClass)
  }

  testWithContext("complex-inheritance-same-root", inheritance / tname"SameTasty" / obj, fundamentalClasses*) {
    //    Any     Mixin { type BarType; def bar: BarType; def getBar(): BarType = bar }
    //     │               │
    //  AnyRef         SubMixin { type BarType = Int; def bar: BarType = 29 }
    //     │               │
    //     └───────┬───────┘
    //             │
    //          WithMixin
    //             │
    //         SubWithMixin

    val SubWithMixinClass = ctx.findStaticClass("inheritance.SameTasty.SubWithMixin")
    val MixinClass = ctx.findStaticClass("inheritance.SameTasty.Mixin")
    val SubMixinClass = ctx.findStaticClass("inheritance.SameTasty.SubMixin")

    val barMethod = SubWithMixinClass.typeRef.member(name"bar")
    assert(clue(barMethod.owner) == SubMixinClass)

    val getBarMethod = SubWithMixinClass.typeRef.member(name"getBar")
    assert(clue(getBarMethod.owner) == MixinClass)

    val BarTypeSym = SubWithMixinClass.typeRef.member(tname"BarType")
    assert(BarTypeSym.isInstanceOf[TypeMemberSymbol])
    assert(clue(BarTypeSym.owner) == SubMixinClass)
  }

  testWithContext(
    "basic-inheritance-different-root",
    inheritanceCrossTasty / tname"Parent",
    (Seq(inheritanceCrossTasty / tname"Child", inheritanceCrossTasty / tname"Sub") ++ fundamentalClasses)*
  ) {
    val ParentClass = ctx.findStaticClass("inheritance.crosstasty.Parent")
    val ChildClass = ctx.findStaticClass("inheritance.crosstasty.Child")
    val SubClass = ctx.findStaticClass("inheritance.crosstasty.Sub")

    val fooMethod = SubClass.typeRef.member(name"foo")
    assert(clue(fooMethod.owner) == ChildClass)

    val getFooMethod = SubClass.typeRef.member(name"getFoo")
    assert(clue(getFooMethod.owner) == ParentClass)

    val FooTypeSym = SubClass.typeRef.member(tname"FooType")
    assert(FooTypeSym.isInstanceOf[TypeMemberSymbol])
    assert(clue(FooTypeSym.owner) == ChildClass)
  }

  testWithContext("MapView.withFilter", name"scala" / name"collection" / tname"MapView") {
    val MapView = ctx.findTopLevelClass("scala.collection.MapView")
    assert(MapView.getDecl(tpnme.RefinedClassMagic).isEmpty)
  }

  testWithContext("consistent-exception-in-parents-issue-168", inheritanceCrossTasty / tname"Child") {
    val ChildClass = ctx.findStaticClass("inheritance.crosstasty.Child")
    intercept[MemberNotFoundException](ChildClass.parents)
    intercept[MemberNotFoundException](ChildClass.parents) // it's the same exception the second time
  }

  testWithContext(
    "resolve-class-mentioning-inner-class",
    name"java" / name"util" / tname"TreeMap",
    name"java" / name"util" / tname"AbstractMap",
    name"java" / name"util" / tname"NavigableMap",
    name"java" / name"util" / tname"SortedMap",
    name"java" / name"util" / tname"Map",
    jlObject,
    jlCloneable,
    javaFunction1,
    jioSerializable
  ) {
    val TreeMap = ctx.findTopLevelClass("java.util.TreeMap")
    val entrySet = TreeMap
      .getDecls(name"entrySet")
      .collectFirst {
        case sym: TermSymbol if !sym.is(Flags.Method) => sym
      }
      .get // private field entrySet: Ljava/util/TreeMap<TK;TV;>.EntrySet;
    val entrySetSelection = entrySet.declaredType match
      case fieldTpe: ExprType =>
        fieldTpe.resultType match
          case sel: TypeRef => sel
          case _            => fail("expected a type selection")
      case _ => fail("entrySet is not an ExprType")
    val expectedMessage =
      "Cannot find member 'EntrySet' in class symbol[class TreeMap] for prefix " +
        "AppliedType(TypeRef(PackageRef(java.util), symbol[class TreeMap]), " +
        "List(TypeRef(NoPrefix, symbol[K]), TypeRef(NoPrefix, symbol[V])))"
    interceptMessage[MemberNotFoundException](expectedMessage)(entrySetSelection.symbol)
  }
}
