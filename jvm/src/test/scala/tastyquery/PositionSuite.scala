package tastyquery

import scala.concurrent.ExecutionContext.Implicits.global
import scala.io.Source
import scala.reflect.TypeTest

import tastyquery.ast.Trees.*
import tastyquery.ast.TypeTrees.*
import tastyquery.ast.Types.*
import tastyquery.ast.Spans.*

import Paths.*

class PositionSuite extends RestrictedUnpicklingSuite {
  val ResourceCodeEnvVar = "TASTY_TEST_SOURCES"

  val empty_class = RootPkg / name"empty_class"
  val simple_trees = RootPkg / name"simple_trees"
  val imports = RootPkg / name"imports"

  private def getCodePath(name: String): String =
    var Array(dir, filename) = name.split('.')
    // A temporary workaround for path
    // TODO: remove the workaround
    if filename == "TraitWithSelf" then filename = "ClassWithSelf"
    s"${System.getenv(ResourceCodeEnvVar)}/main/scala/$dir/$filename.scala"

  def testUnpickleWithCode(name: String, path: TopLevelDeclPath)(using munit.Location)(
    body: (Tree, String) => Unit
  ): Unit =
    testUnpickleWithCode(new munit.TestOptions(name), path)(body)
  end testUnpickleWithCode

  def testUnpickleWithCode(testOptions: munit.TestOptions, path: TopLevelDeclPath)(
    using munit.Location
  )(body: (Tree, String) => Unit): Unit =
    test(testOptions) {
      for (base, tree) <- findTopLevelTasty(path)() yield
        val codePath = getCodePath(path.rootClassName)
        val code = Source.fromFile(codePath).mkString
        body(tree, code)
    }
  end testUnpickleWithCode

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

  testUnpickleWithCode("var-def", simple_trees / tname"Var") { (tree, code) =>
    assertEquals(collectCode[ValDef](tree, code), List("var x = 1"))
  }

  testUnpickleWithCode("literal", simple_trees / tname"Constants") { (tree, code) =>
    assertEquals(
      collectCode[Literal](tree, code),
      List("()", "false", "true", "1", "1", "'a'", "1", "1L", "1.1f", "1.1d", "\"string\"", "null")
    )
  }

  testUnpickleWithCode("assign", simple_trees / tname"Assign") { (tree, code) =>
    assertEquals(collectCode[Assign](tree, code), List("y = x"))
  }

  testUnpickleWithCode("apply", simple_trees / tname"EtaExpansion") { (tree, code) =>
    assertEquals(collectCode[Apply](tree, code), List("f(0)", "takesFunction(intMethod)"))
  }

  /** Control structures */

  testUnpickleWithCode("if", simple_trees / tname"If") { (tree, code) =>
    assertEquals(collectCode[If](tree, code), List("if (x < 0) -x else x"))
  }

  testUnpickleWithCode("while", simple_trees / tname"While") { (tree, code) =>
    assertEquals(
      collectCode[While](tree, code),
      List("""while (true) {
             |      ()
             |    }""".stripMargin)
    )
  }

  testUnpickleWithCode("match", simple_trees / tname"Match") { (tree, code) =>
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

  testUnpickleWithCode("case-def", simple_trees / tname"Match") { (tree, code) =>
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

  testUnpickleWithCode("bind", simple_trees / tname"Bind") { (tree, code) =>
    assertEquals(collectCode[Bind](tree, code), List("t @ y", "y", "s: String", "k @ Some(_)"))
  }

  /** Functions */

  testUnpickleWithCode("def-def", simple_trees / tname"Function") { (tree, code) =>
    assertEquals(collectCode[DefDef](tree, code), List("(x: Int) => x + 1", "() => ()"))
  }

  testUnpickleWithCode("def-def-nested", simple_trees / tname"NestedMethod") { (tree, code) =>
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

  testUnpickleWithCode("named-arg", simple_trees / tname"NamedArgument") { (tree, code) =>
    assertEquals(collectCode[NamedArg](tree, code), List("second = 1"))
  }

  testUnpickleWithCode("block", simple_trees / tname"Block") { (tree, code) =>
    assertEquals(
      collectCode[Block](tree, code),
      List("""{
             |    val a = 1
             |    val b = 2
             |    ()
             |  }""".stripMargin)
    )
  }

  testUnpickleWithCode("lambda", simple_trees / tname"Function") { (tree, code) =>
    assertEquals(
      collectCode[Lambda](tree, code),
      // NoSpan is the expected behavior
      Nil
    )
  }

  testUnpickleWithCode("return", simple_trees / tname"Return") { (tree, code) =>
    assertEquals(collectCode[Return](tree, code), List("return 1"))
  }

  /** Classes */

  testUnpickleWithCode("class", simple_trees / tname"InnerClass") { (tree, code) =>
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

  testUnpickleWithCode("super", simple_trees / tname"Super") { (tree, code) =>
    assertEquals(collectCode[Super](tree, code), List("super", "super[Base]"))
  }

  testUnpickleWithCode("class-with-self", simple_trees / tname"ClassWithSelf") { (tree, code) =>
    // ignore because the span of Self is impossible to construct
    assertEquals(collectCode[ValDef](tree, code), Nil)
  }

  testUnpickleWithCode("trait-with-self", simple_trees / tname"TraitWithSelf") { (tree, code) =>
    // ignore because the span of Self is impossible to construct
    assertEquals(collectCode[ValDef](tree, code), List("ClassWithSelf"))
  }

  /** Import and export */

  testUnpickleWithCode("import", imports / tname"Import") { (tree, code) =>
    assertEquals(collectCode[Import](tree, code), List("import imported_files.A"))
  }

  testUnpickleWithCode("import-selector-multiple", imports / tname"MultipleImports") { (tree, code) =>
    assertEquals(collectCode[ImportSelector](tree, code), List("A", "B"))
  }

  testUnpickleWithCode("import-selector-bound", imports / tname"ImportGivenWithBound") { (tree, code) =>
    assertEquals(collectCode[ImportSelector](tree, code), List("A", "given A"))
  }

  testUnpickleWithCode("import-selector-renamed", imports / tname"RenamedImport") { (tree, code) =>
    assertEquals(collectCode[ImportSelector](tree, code), List("A => ClassA"))
  }

  testUnpickleWithCode("export", simple_trees / tname"Export") { (tree, code) =>
    assertEquals(
      collectCode[Export](tree, code),
      List("export first.status", "export second.{status => _, *}", "export givens.given AnyRef")
    )
  }

  /** Throw and try-catch */

  testUnpickleWithCode("throw", simple_trees / tname"ThrowException") { (tree, code) =>
    assertEquals(collectCode[Throw](tree, code), List("throw new NullPointerException"))
  }

  testUnpickleWithCode("try", simple_trees / tname"TryCatch") { (tree, code) =>
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

  testUnpickleWithCode("typed", simple_trees / tname"Typed") { (tree, code) =>
    assertEquals(collectCode[Typed](tree, code), List("1: Int"))
  }

  testUnpickleWithCode("type-member", simple_trees / tname"TypeMember") { (tree, code) =>
    assertEquals(
      collectCode[TypeMember](tree, code),
      List(
        "type TypeMember = Int",
        "type AbstractType",
        "type AbstractWithBounds >: Null <: Product",
        "opaque type Opaque = Int",
        "opaque type OpaqueWithBounds >: Null <: Product = Null"
      )
    )
  }

  testUnpickleWithCode("type-apply", simple_trees / tname"TypeApply") { (tree, code) =>
    assertEquals(collectCode[TypeApply](tree, code), List("Seq[Int]", "A[Int, Seq[String]]"))
  }

  testUnpickleWithCode("type-ident", simple_trees / tname"Typed") { (tree, code) =>
    assertEquals(collectCodeT[TypeIdent](tree, code), List("Int"))
  }

  testUnpickleWithCode("singleton-type", simple_trees / tname"SingletonType") { (tree, code) =>
    assertEquals(collectCodeT[SingletonTypeTree](tree, code), List("x.type"))
  }

  testUnpickleWithCode("refined-type", simple_trees / tname"RefinedType") { (tree, code) =>
    assertEquals(collectCodeT[RefinedTypeTree](tree, code), Nil)
  }

  testUnpickleWithCode("by-name-type", simple_trees / tname"ByNameParameter") { (tree, code) =>
    assertEquals(collectCodeT[ByNameTypeTree](tree, code), List("=> Int"))
  }

  testUnpickleWithCode("applied-type", simple_trees / tname"AppliedTypeAnnotation") { (tree, code) =>
    assertEquals(collectCodeT[AppliedTypeTree](tree, code), List("Option[Int]"))
  }

  testUnpickleWithCode("select-type", simple_trees / tname"SelectType") { (tree, code) =>
    assertEquals(collectCodeT[SelectTypeTree](tree, code), List("util.Random"))
  }

  testUnpickleWithCode("annotated-type", simple_trees / tname"VarargFunction") { (tree, code) =>
    assertEquals(collectCodeT[AnnotatedTypeTree](tree, code), List("Int*"))
  }

  testUnpickleWithCode("match-type".ignore, simple_trees / tname"MatchType") { (tree, code) =>
    assertEquals(collectCodeT[MatchTypeTree](tree, code), List(""))
  }

  testUnpickleWithCode("type-tree-bind".ignore, simple_trees / tname"MatchType") { (tree, code) =>
    assertEquals(collectCodeT[TypeTreeBind](tree, code), List(""))
  }

  testUnpickleWithCode("bounded-type".ignore, simple_trees / tname"TypeMember") { (tree, code) =>
    assertEquals(collectCodeT[BoundedTypeTree](tree, code), List(""))
  }

  testUnpickleWithCode("named-type-bounds".ignore, simple_trees / tname"MatchType") { (tree, code) =>
    assertEquals(collectCodeT[NamedTypeBoundsTree](tree, code), List(""))
  }

  testUnpickleWithCode("type-lambda", simple_trees / tname"TypeLambda") { (tree, code) =>
    assertEquals(collectCodeT[TypeLambdaTree](tree, code), List("[X] =>> List[X]"))
  }

  /** Inlined */

  testUnpickleWithCode("inlined", simple_trees / tname"InlinedCall") { (tree, code) =>
    assertEquals(collectCode[Inlined](tree, code), List("new withInlineMethod.Inner().inlined(0)", "arg"))
  }

  testUnpickleWithCode("shared-type", simple_trees / tname"SharedType") { (tree, code) =>
    assertEquals(collectCode[Ident](tree, code), List("println", "println"))
  }

}
