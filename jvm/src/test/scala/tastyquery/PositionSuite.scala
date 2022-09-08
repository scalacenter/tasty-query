package tastyquery

import scala.io.Source
import scala.reflect.TypeTest

import tastyquery.ast.Trees.*
import tastyquery.ast.TypeTrees.*
import tastyquery.ast.Types.*
import tastyquery.ast.Spans.*

import Paths.*

class PositionSuite extends RestrictedUnpicklingSuite {
  val ResourceCodeProperty = "test-resources-code"

  val empty_class = RootPkg / name"empty_class"
  val simple_trees = RootPkg / name"simple_trees"
  val imports = RootPkg / name"imports"

  private def getCodePath(name: String): String =
    var Array(dir, filename) = name.split('.')
    // A temporary workaround for path
    // TODO: remove the workaround
    if filename == "TraitWithSelf" then filename = "ClassWithSelf"
    s"${System.getProperty(ResourceCodeProperty)}/main/scala/$dir/$filename.scala"

  private def unpickleWithCode(path: TopLevelDeclPath): (Tree, String) = {
    val (base, tree) = findTopLevelTasty(path)()
    val codePath = getCodePath(path.rootClassName)
    val code = Source.fromFile(codePath).mkString
    (tree, code)
  }

  private def treeToCode(tree: Tree, code: String): (Int, String) =
    if tree.span.exists then (tree.span.start, code.slice(tree.span.start, tree.span.end)) else (-1, "")

  private def treeToCode(tree: TypeTree, code: String): (Int, String) =
    if tree.span.exists then (tree.span.start, code.slice(tree.span.start, tree.span.end)) else (-1, "")

  private def collectCode[T <: Tree](tree: Tree, code: String)(using tt: TypeTest[Tree, T]): List[String] =
    tree
      .walkTree[List[(Int, String)]]({
        case tt(t: T) => List(treeToCode(t, code))
        case _        => Nil
      })(_ ::: _, Nil)
      .distinct
      .map(_._2)
      .filter(_ != "")

  private def collectCodeT[T <: TypeTree](tree: Tree, code: String)(using tt: TypeTest[TypeTree, T]): List[String] =
    tree
      .walkTypeTrees[List[(Int, String)]]({
        case tt(t: T) => List(treeToCode(t, code))
        case _        => Nil
      })(_ ::: _, Nil)
      .distinct
      .map(_._2)
      .filter(_ != "")

  /** Basics */

  test("var-def") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Var")
    assertEquals(collectCode[ValDef](tree, code), List("var x = 1"))
  }

  test("literal") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Constants")
    assertEquals(
      collectCode[Literal](tree, code),
      List("()", "false", "true", "1", "1", "'a'", "1", "1L", "1.1f", "1.1d", "\"string\"", "null")
    )
  }

  test("assign") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Assign")
    assertEquals(collectCode[Assign](tree, code), List("y = x"))
  }

  test("apply") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"EtaExpansion")
    assertEquals(collectCode[Apply](tree, code), List("f(0)", "takesFunction(intMethod)"))
  }

  /** Control structures */

  test("if") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"If")
    assertEquals(collectCode[If](tree, code), List("if (x < 0) -x else x"))
  }

  test("while") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"While")
    assertEquals(
      collectCode[While](tree, code),
      List("""while (true) {
             |      ()
             |    }""".stripMargin)
    )
  }

  test("match") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Match")
    assertEquals(
      collectCode[Match](tree, code),
      List("""x match {
             |    case 0 => 0
             |    case 1 | -1 | 2 => x + 1
             |    case 7 if x == 7 => x - 1
             |    case 3 | 4 | 5 if x < 5 => 0
             |    case _ if (x % 2 == 0) => x / 2
             |    case _ => -x
             |  }""".stripMargin)
    )
  }

  test("case-def") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Match")
    assertEquals(
      collectCode[CaseDef](tree, code),
      List(
        "case 0 => 0",
        "case 1 | -1 | 2 => x + 1",
        "case 7 if x == 7 => x - 1",
        "case 3 | 4 | 5 if x < 5 => 0",
        "case _ if (x % 2 == 0) => x / 2",
        "case _ => -x"
      )
    )
  }

  test("bind") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Bind")
    assertEquals(collectCode[Bind](tree, code), List("t @ y", "y", "s: String", "k @ Some(_)"))
  }

  /** Functions */

  test("def-def") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Function")
    assertEquals(collectCode[DefDef](tree, code), List("(x: Int) => x + 1", "() => ()"))
  }

  test("def-def-nested") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"NestedMethod")
    assertEquals(
      collectCode[DefDef](tree, code),
      List(
        """def outerMethod: Unit = {
          |    def innerMethod: Unit = ()
          |  }""".stripMargin,
        "def innerMethod: Unit = ()"
      )
    )
  }

  test("named-arg") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"NamedArgument")
    assertEquals(collectCode[NamedArg](tree, code), List("second = 1"))
  }

  test("block") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Block")
    assertEquals(
      collectCode[Block](tree, code),
      List("""{
             |    val a = 1
             |    val b = 2
             |    ()
             |  }""".stripMargin)
    )
  }

  test("lambda") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Function")
    assertEquals(
      collectCode[Lambda](tree, code),
      // NoSpan is the expected behavior
      Nil
    )
  }

  test("return") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Return")
    assertEquals(collectCode[Return](tree, code), List("return 1"))
  }

  /** Classes */

  test("class") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"InnerClass")
    assertEquals(
      collectCode[ClassDef](tree, code),
      List(
        """class InnerClass {
          |  val innerInstance = new Inner
          |
          |  class Inner
          |}""".stripMargin,
        "class Inner"
      )
    )
  }

  test("super") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Super")
    assertEquals(collectCode[Super](tree, code), List("super", "super[Base]"))
  }

  test("class-with-self") {
    // ignore because the span of Self is impossible to construct
    val (tree, code) = unpickleWithCode(simple_trees / tname"ClassWithSelf")
    assertEquals(collectCode[ValDef](tree, code), Nil)
  }

  test("trait-with-self") {
    // ignore because the span of Self is impossible to construct
    val (tree, code) = unpickleWithCode(simple_trees / tname"TraitWithSelf")
    assertEquals(collectCode[ValDef](tree, code), List("ClassWithSelf"))
  }

  /** Import and export */

  test("import") {
    val (tree, code) = unpickleWithCode(imports / tname"Import")
    assertEquals(collectCode[Import](tree, code), List("import imported_files.A"))
  }

  test("import-selector-multiple") {
    val (tree, code) = unpickleWithCode(imports / tname"MultipleImports")
    assertEquals(collectCode[ImportSelector](tree, code), List("A", "B"))
  }

  test("import-selector-bound") {
    val (tree, code) = unpickleWithCode(imports / tname"ImportGivenWithBound")
    assertEquals(collectCode[ImportSelector](tree, code), List("A", "given A"))
  }

  test("import-selector-renamed") {
    val (tree, code) = unpickleWithCode(imports / tname"RenamedImport")
    assertEquals(collectCode[ImportSelector](tree, code), List("A => ClassA"))
  }

  test("export") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Export")
    assertEquals(
      collectCode[Export](tree, code),
      List("export first.status", "export second.{status => _, *}", "export givens.given AnyRef")
    )
  }

  /** Throw and try-catch */

  test("throw") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"ThrowException")
    assertEquals(collectCode[Throw](tree, code), List("throw new NullPointerException"))
  }

  test("try") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"TryCatch")
    assertEquals(
      collectCode[Try](tree, code),
      List("""try {
             |      ThrowException().f()
             |      1
             |    } catch {
             |      case _ => 0
             |    } finally {
             |      ()
             |    }""".stripMargin)
    )
  }

  /** Types */

  test("typed") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Typed")
    assertEquals(collectCode[Typed](tree, code), List("1: Int"))
  }

  test("type-member") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"TypeMember")
    assertEquals(
      collectCode[TypeMember](tree, code),
      List(
        "type TypeMember = Int",
        "type AbstractType",
        "type AbstractWithBounds >: Null <: AnyRef",
        "opaque type Opaque = Int",
        "opaque type OpaqueWithBounds >: Null <: AnyRef = Null"
      )
    )
  }

  test("type-apply") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"TypeApply")
    assertEquals(collectCode[TypeApply](tree, code), List("Seq[Int]", "A[Int, Seq[String]]"))
  }

  test("type-ident") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"Typed")
    assertEquals(collectCodeT[TypeIdent](tree, code), List("Int"))
  }

  test("singleton-type") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"SingletonType")
    assertEquals(collectCodeT[SingletonTypeTree](tree, code), List("x.type"))
  }

  test("refined-type") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"RefinedType")
    assertEquals(collectCodeT[RefinedTypeTree](tree, code), Nil)
  }

  test("by-name-type") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"ByNameParameter")
    assertEquals(collectCodeT[ByNameTypeTree](tree, code), List("=> Int"))
  }

  test("applied-type") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"AppliedTypeAnnotation")
    assertEquals(collectCodeT[AppliedTypeTree](tree, code), List("Option[Int]"))
  }

  test("select-type") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"SelectType")
    assertEquals(collectCodeT[SelectTypeTree](tree, code), List("util.Random"))
  }

  test("annotated-type") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"VarargFunction")
    assertEquals(collectCodeT[AnnotatedTypeTree](tree, code), List("Int*"))
  }

  test("match-type".ignore) {
    val (tree, code) = unpickleWithCode(simple_trees / tname"MatchType")
    assertEquals(collectCodeT[MatchTypeTree](tree, code), List(""))
  }

  test("type-tree-bind".ignore) {
    val (tree, code) = unpickleWithCode(simple_trees / tname"MatchType")
    assertEquals(collectCodeT[TypeTreeBind](tree, code), List(""))
  }

  test("bounded-type".ignore) {
    val (tree, code) = unpickleWithCode(simple_trees / tname"TypeMember")
    assertEquals(collectCodeT[BoundedTypeTree](tree, code), List(""))
  }

  test("named-type-bounds".ignore) {
    val (tree, code) = unpickleWithCode(simple_trees / tname"MatchType")
    assertEquals(collectCodeT[NamedTypeBoundsTree](tree, code), List(""))
  }

  test("type-lambda") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"TypeLambda")
    assertEquals(collectCodeT[TypeLambdaTree](tree, code), List("[X] =>> List[X]"))
  }

  /** Inlined */

  test("inlined") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"InlinedCall")
    assertEquals(collectCode[Inlined](tree, code), List("new withInlineMethod.Inner().inlined(0)", "arg"))
  }

  test("shared-type") {
    val (tree, code) = unpickleWithCode(simple_trees / tname"SharedType")
    assertEquals(collectCode[Ident](tree, code), List("println", "println"))
  }

}
