package tastyquery

import scala.concurrent.ExecutionContext.Implicits.global
import scala.reflect.TypeTest

import tastyquery.Names.*
import tastyquery.Trees.*
import tastyquery.Types.*
import tastyquery.Spans.*

class PositionSuite extends RestrictedUnpicklingSuite {
  private def getCodeRelPath(name: String): String =
    var Array(dir, filename) = name.split('.')
    // A temporary workaround for path
    // TODO: remove the workaround
    if filename == "TraitWithSelf" then filename = "ClassWithSelf"
    s"main/scala/$dir/$filename.scala"

  def testUnpickleWithCode(name: String, rootSymbolPath: String)(using munit.Location)(
    body: (Tree, String) => Unit
  ): Unit =
    testUnpickleWithCode(new munit.TestOptions(name), rootSymbolPath)(body)
  end testUnpickleWithCode

  def testUnpickleWithCode(testOptions: munit.TestOptions, rootSymbolPath: String)(
    using munit.Location
  )(body: (Tree, String) => Unit): Unit =
    test(testOptions) {
      val pathStrs = rootSymbolPath.split('.').toList
      val path = pathStrs.init.map(termName(_)) :+ typeName(pathStrs.last)
      for (base, tree) <- findTopLevelTasty(rootSymbolPath)() yield
        val codePath = getCodeRelPath(rootSymbolPath)
        val code = tastyquery.testutil.TestPlatform.readResourceCodeFile(codePath)
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

  /** Basics */

  testUnpickleWithCode("var-def", "simple_trees.Var") { (tree, code) =>
    assertEquals(collectCode[ValDef](tree, code), List("var x = 1"))
  }

  testUnpickleWithCode("literal", "simple_trees.Constants") { (tree, code) =>
    assertEquals(
      collectCode[Literal](tree, code),
      List("()", "false", "true", "1", "1", "'a'", "1", "1L", "1.1f", "1.1d", "\"string\"", "null")
    )
  }

  testUnpickleWithCode("assign", "simple_trees.Assign") { (tree, code) =>
    assertEquals(collectCode[Assign](tree, code), List("y = x"))
  }

  testUnpickleWithCode("apply", "simple_trees.EtaExpansion") { (tree, code) =>
    assertEquals(collectCode[Apply](tree, code), List("f(0)", "takesFunction(intMethod)"))
  }

  /** Control structures */

  testUnpickleWithCode("if", "simple_trees.If") { (tree, code) =>
    assertEquals(collectCode[If](tree, code), List("if (x < 0) -x else x"))
  }

  testUnpickleWithCode("while", "simple_trees.While") { (tree, code) =>
    assertEquals(
      collectCode[While](tree, code),
      List("""while (true) {
             |      ()
             |    }""".stripMargin)
    )
  }

  testUnpickleWithCode("match", "simple_trees.Match") { (tree, code) =>
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

  testUnpickleWithCode("case-def", "simple_trees.Match") { (tree, code) =>
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

  testUnpickleWithCode("bind", "simple_trees.Bind") { (tree, code) =>
    assertEquals(collectCode[Bind](tree, code), List("t @ y", "y", "s: String", "k @ Some(_)"))
  }

  /** Functions */

  testUnpickleWithCode("def-def", "simple_trees.Function") { (tree, code) =>
    assertEquals(
      collectCode[DefDef](tree, code),
      List(
        "(x: Int) => x + 1",
        "() => ()",
        "T] => T => T", // TODO Improve this
        "T] => (x: T) => x", // TODO Improve this
        "(x: Any) => x.type",
        "x => x"
      )
    )
  }

  testUnpickleWithCode("def-def-nested", "simple_trees.NestedMethod") { (tree, code) =>
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

  testUnpickleWithCode("named-arg", "simple_trees.NamedArgument") { (tree, code) =>
    assertEquals(collectCode[NamedArg](tree, code), List("second = 1"))
  }

  testUnpickleWithCode("block", "simple_trees.Block") { (tree, code) =>
    assertEquals(
      collectCode[Block](tree, code),
      List("""{
             |    val a = 1
             |    val b = 2
             |    ()
             |  }""".stripMargin)
    )
  }

  testUnpickleWithCode("lambda", "simple_trees.Function") { (tree, code) =>
    assertEquals(
      collectCode[Lambda](tree, code),
      // NoSpan is the expected behavior
      Nil
    )
  }

  testUnpickleWithCode("return", "simple_trees.Return") { (tree, code) =>
    assertEquals(collectCode[Return](tree, code), List("return 1"))
  }

  /** Classes */

  testUnpickleWithCode("class", "simple_trees.InnerClass") { (tree, code) =>
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

  testUnpickleWithCode("super", "simple_trees.Super") { (tree, code) =>
    assertEquals(
      collectCode[Super](tree, code),
      List(
        "super",
        "super[Base]",
        "super",
        "super[Base]",
        "super",
        "super[Base]",
        "super[BaseTrait]",
        "super",
        "super[Base]",
        "super[BaseTrait]",
        "super",
        "super[BaseTrait]",
        "super",
        "super[BaseTrait]"
      )
    )
  }

  testUnpickleWithCode("class-with-self", "simple_trees.ClassWithSelf") { (tree, code) =>
    // ignore because the span of Self is impossible to construct
    assertEquals(collectCode[SelfDef](tree, code), Nil)
  }

  testUnpickleWithCode("trait-with-self", "simple_trees.TraitWithSelf") { (tree, code) =>
    // ignore because the span of Self is impossible to construct
    assertEquals(collectCode[SelfDef](tree, code), List("ClassWithSelf"))
  }

  /** Import and export */

  testUnpickleWithCode("import", "imports.Import") { (tree, code) =>
    assertEquals(collectCode[Import](tree, code), List("import imported_files.A"))
  }

  testUnpickleWithCode("import-selector-multiple", "imports.MultipleImports") { (tree, code) =>
    assertEquals(collectCode[ImportSelector](tree, code), List("A", "B"))
  }

  testUnpickleWithCode("import-selector-bound", "imports.ImportGivenWithBound") { (tree, code) =>
    assertEquals(collectCode[ImportSelector](tree, code), List("A", "given A"))
  }

  testUnpickleWithCode("import-selector-renamed", "imports.RenamedImport") { (tree, code) =>
    assertEquals(collectCode[ImportSelector](tree, code), List("A => ClassA"))
  }

  testUnpickleWithCode("export", "simple_trees.Export") { (tree, code) =>
    assertEquals(
      collectCode[Export](tree, code),
      List("export first.status", "export second.{status => _, *}", "export givens.given AnyRef")
    )
  }

  /** Throw and try-catch */

  testUnpickleWithCode("throw", "simple_trees.ThrowException") { (tree, code) =>
    assertEquals(collectCode[Throw](tree, code), List("throw new NullPointerException"))
  }

  testUnpickleWithCode("try", "simple_trees.TryCatch") { (tree, code) =>
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

  testUnpickleWithCode("typed", "simple_trees.Typed") { (tree, code) =>
    assertEquals(collectCode[Typed](tree, code), List("1: Int"))
  }

  testUnpickleWithCode("type-member", "simple_trees.TypeMember") { (tree, code) =>
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

  testUnpickleWithCode("type-apply", "simple_trees.TypeApply") { (tree, code) =>
    assertEquals(collectCode[TypeApply](tree, code), List("Seq[Int]", "A[Int, Seq[String]]"))
  }

  testUnpickleWithCode("type-ident", "simple_trees.Typed") { (tree, code) =>
    assertEquals(collectCode[TypeIdent](tree, code), List("Int"))
  }

  testUnpickleWithCode("singleton-type", "simple_trees.SingletonType") { (tree, code) =>
    assertEquals(collectCode[SingletonTypeTree](tree, code), List("x.type"))
  }

  testUnpickleWithCode("refined-type", "simple_trees.RefinedType") { (tree, code) =>
    assertEquals(collectCode[RefinedTypeTree](tree, code), List("{ def foo(using Int): Int }"))
  }

  testUnpickleWithCode("by-name-type", "simple_trees.ByNameParameter") { (tree, code) =>
    assertEquals(collectCode[ByNameTypeTree](tree, code), List("=> Int"))
  }

  testUnpickleWithCode("applied-type", "simple_trees.AppliedTypeAnnotation") { (tree, code) =>
    assertEquals(collectCode[AppliedTypeTree](tree, code), List("Option[Int]"))
  }

  testUnpickleWithCode("select-type", "simple_trees.SelectType") { (tree, code) =>
    assertEquals(collectCode[SelectTypeTree](tree, code), List("util.Random"))
  }

  testUnpickleWithCode("annotated-type", "simple_trees.VarargFunction") { (tree, code) =>
    assertEquals(collectCode[AnnotatedTypeTree](tree, code), List("Int*"))
  }

  testUnpickleWithCode("match-type", "simple_trees.MatchType") { (tree, code) =>
    assertEquals(
      collectCode[MatchTypeTree](tree, code),
      List(
        """X match {
          |    case Int => String
          |  }""".stripMargin,
        """X match {
          |    case _ => Int
          |  }""".stripMargin,
        """X match {
          |    case List[t] => t
          |  }""".stripMargin
      )
    )
  }

  testUnpickleWithCode("type-tree-bind", "simple_trees.MatchType") { (tree, code) =>
    assertEquals(collectCode[TypeTreeBind](tree, code), List("t", "t"))
  }

  testUnpickleWithCode("named-type-bounds", "simple_trees.MatchType") { (tree, code) =>
    assertEquals(collectCode[NamedTypeBoundsTree](tree, code), List("t", "t"))
  }

  testUnpickleWithCode("type-definition-tree-1", "simple_trees.TypeMember") { (tree, code) =>
    assertEquals(collectCode[TypeDefinitionTree](tree, code), List("Int", ">: Null <: Product", "Int"))
  }

  testUnpickleWithCode("type-definition-tree-2", "simple_trees.TypeLambda") { (tree, code) =>
    assertEquals(collectCode[TypeDefinitionTree](tree, code), List("[X] =>> List[X]", "List[X]"))
  }

  /** Inlined */

  testUnpickleWithCode("inlined", "simple_trees.InlinedCall") { (tree, code) =>
    assertEquals(collectCode[Inlined](tree, code), List("new withInlineMethod.Inner().inlined(0)", "arg"))
  }

  testUnpickleWithCode("shared-type", "simple_trees.SharedType") { (tree, code) =>
    assertEquals(collectCode[Ident](tree, code), List("println", "println"))
  }

}
