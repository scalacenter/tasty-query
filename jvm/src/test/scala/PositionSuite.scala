import tastyquery.Contexts
import tastyquery.Contexts.FileContext
import tastyquery.ast.Trees._
import tastyquery.reader.TastyUnpickler
import tastyquery.reader.PositionUnpickler
import dotty.tools.dotc.util.Spans.{Span, NoSpan}

import scala.reflect.TypeTest
import java.nio.file.{Files, Paths}
import scala.util.control.Exception.Catch

class PositionSuite extends BaseUnpicklingSuite {

  val ResourceCodeProperty = "test-resources-code"

  def getCodePath(name: String): String =
    s"${System.getProperty(ResourceCodeProperty)}/main/scala/$name.scala"

  def unpickleWithCode(filename: String)(using ctx: FileContext = Contexts.empty(filename)): (Tree, String) = {
    val resourcePath = getResourcePath(filename)
    val codePath = getCodePath(filename)
    val bytes = Files.readAllBytes(Paths.get(resourcePath))
    val code = Files.readString(Paths.get(codePath))

    val unpickler = new TastyUnpickler(bytes)
    val tree = unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler(
      unpickler.unpickle(new TastyUnpickler.PositionSectionUnpickler))).get.unpickle(using ctx).head
    (tree, code)
  }

  private def treeToCode(tree: Tree, code: String): String =
    if tree.span.exists then code.substring(tree.span.start, tree.span.end) else ""

  private def printTreeWithCode(tree: Tree, code: String): Unit =
    tree.walkTree(t => {
      println(t)
      println("-" * 40)
      if (t.span.exists) {
        println(treeToCode(t, code))
      } else {
        println(t.span)
      }
      println("=" * 40)
    })
  
  private def collectCode[T <: Tree](tree: Tree, code: String)
      (using tt: TypeTest[Tree, T]): List[String] =
    tree.walkTree[List[String]]({
      case tt(t: T) => List(treeToCode(t, code))
      case _ => Nil
    })(_ ::: _, Nil).filter(_ != "")

  /** Basics */

  test("var-def") {
    val (tree, code) = unpickleWithCode("simple_trees/Var")
    assertEquals(
      collectCode[ValDef](tree, code),
      List("var x = 1")
    )
  }

  test("literal") {
    val (tree, code) = unpickleWithCode("simple_trees/Constants")
    assertEquals(
      collectCode[Literal](tree, code),
      List(
        "()",
        "false",
        "true",
        "1",
        "1",
        "'a'",
        "1",
        "1L",
        "1.1f",
        "1.1d",
        "\"string\"",
        "null"
      )
    )
  }

  test("assign") {
    val (tree, code) = unpickleWithCode("simple_trees/Assign")
    assertEquals(
      collectCode[Assign](tree, code),
      List("y = x")
    )
  }

  test("apply") {
    val (tree, code) = unpickleWithCode("simple_trees/EtaExpansion")
    assertEquals(
      collectCode[Apply](tree, code), 
      List(
        "f(0)",
        "takesFunction(intMethod)",
        "intMethod"
      )
    )
  }

  /** Control structures */

  test("if") {
    val (tree, code) = unpickleWithCode("simple_trees/If")
    assertEquals(
      collectCode[If](tree, code),
      List("if (x < 0) -x else x")
    )
  }

  test("while") {
    val (tree, code) = unpickleWithCode("simple_trees/While")
    assertEquals(
      collectCode[While](tree, code),
      List(
        """while (true) {
        |      ()
        |    }""".stripMargin
      )
    )
  }

  test("match") {
    val (tree, code) = unpickleWithCode("simple_trees/Match")
    assertEquals(
      collectCode[Match](tree, code),
      List(
        """x match {
        |    case 0 => 0
        |    case 1 | -1 | 2 => x + 1
        |    case 7 if x == 7 => x - 1
        |    case 3 | 4 | 5 if x < 5 => 0
        |    case _ if (x % 2 == 0) => x / 2
        |    case _ => -x
        |  }""".stripMargin
      )
    )
  }

  test("case-def") {
    val (tree, code) = unpickleWithCode("simple_trees/Match")
    assertEquals(
      collectCode[CaseDef](tree, code), 
      Nil
    )
  }

  test("bind") {
    val (tree, code) = unpickleWithCode("simple_trees/Bind")
    assertEquals(
      collectCode[Bind](tree, code), 
      List(
        "t @ y",
        "y",
        "s: String",
        "k @ Some(_)"
      )
    )
  }

  /** Functions */

  test("def-def") {
    val (tree, code) = unpickleWithCode("simple_trees/Function")
    assertEquals(
      collectCode[DefDef](tree, code),
      List(
        "(x: Int) => x + 1",
        "() => ()"
      )
    )
  }

  test("def-def-nested") {
    val (tree, code) = unpickleWithCode("simple_trees/NestedMethod")
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
    val (tree, code) = unpickleWithCode("simple_trees/NamedArgument")
    assertEquals(
      collectCode[NamedArg](tree, code),
      List("second = 1")
    )
  }

  test("block") {
    val (tree, code) = unpickleWithCode("simple_trees/Block")
    assertEquals(
      collectCode[Block](tree, code),
      List(
        """{
        |    val a = 1
        |    val b = 2
        |    ()
        |  }""".stripMargin
      )
    )
  }

  test("lambda") {
    val (tree, code) = unpickleWithCode("simple_trees/Function")
    assertEquals(
      collectCode[Lambda](tree, code),
      // NoSpan is the expected behavior
      Nil
    )
  }

  test("return") {
    val (tree, code) = unpickleWithCode("simple_trees/Return")
    assertEquals(
      collectCode[Return](tree, code),
      List("return 1")
    )
    assertEquals(
      collectCode[Ident](tree, code),
      List("1")
    )
  }

  /** Classes */

  test("class") {
    val (tree, code) = unpickleWithCode("simple_trees/InnerClass")
    assertEquals(
      collectCode[Class](tree, code), 
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
    val (tree, code) = unpickleWithCode("simple_trees/Super")
    assertEquals(
      collectCode[Super](tree, code), 
      List(
        "super",
        "super[Base]"
      )
    )
  }

  test("self") {
    val (tree, code) = unpickleWithCode("simple_trees/ClassWithSelf")
    assertEquals(
      collectCode[ValDef](tree, code), 
      List(
        "self: ClassWithSelf =>"
      )
    )
  }

  /** Import and export */

  test("import") {
    val (tree, code) = unpickleWithCode("imports/Import")
    assertEquals(
      collectCode[Import](tree, code), 
      List("import imported_files.A")
    )
  }

  test("import-selector-multiple") {
    val (tree, code) = unpickleWithCode("imports/MultipleImports")
    assertEquals(
      collectCode[ImportSelector](tree, code), 
      List("A", "B")
    )
  }

  test("import-selector-bound") {
    val (tree, code) = unpickleWithCode("imports/ImportGivenWithBound")
    assertEquals(
      collectCode[ImportSelector](tree, code), 
      List("A", "given A")
    )
  }

  test("import-selector-renamed") {
    val (tree, code) = unpickleWithCode("imports/RenamedImport")
    assertEquals(
      collectCode[ImportSelector](tree, code), 
      List("A => ClassA")
    )
  }

  test("export") {
    val (tree, code) = unpickleWithCode("simple_trees/Export")
    assertEquals(
      collectCode[Export](tree, code), 
      List(
        "export first.status",
        "export second.{status => _, *}",
        "export givens.given AnyRef"
      )
    )
  }

  /** Throw and try-catch */

  test("throw") {
    val (tree, code) = unpickleWithCode("simple_trees/ThrowException")
    assertEquals(
      collectCode[Throw](tree, code), 
      List("throw new NullPointerException")
    )
  }

  test("try") {
    val (tree, code) = unpickleWithCode("simple_trees/TryCatch")
    assertEquals(
      collectCode[Try](tree, code), 
      List(
        """try {
        |      ThrowException().f()
        |      1
        |    } catch {
        |      case _ => 0
        |    } finally {
        |      ()
        |    }""".stripMargin
      )
    )
  }

  /** Types */

  test("typed") {
    val (tree, code) = unpickleWithCode("simple_trees/Typed")
    assertEquals(
      collectCode[Typed](tree, code), 
      List("1: Int")
    )
  }

  test("type-member") {
    val (tree, code) = unpickleWithCode("simple_trees/TypeMember")
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
    val (tree, code) = unpickleWithCode("simple_trees/TypeApply")
    assertEquals(
      collectCode[TypeApply](tree, code), 
      List("Seq(1)")
    )
  }

  /** Inlined */

  test("inlined") {
    val (tree, code) = unpickleWithCode("simple_trees/InlinedCall")
    assertEquals(
      collectCode[Inlined](tree, code), 
      List(
        "new withInlineMethod.Inner().inlined(0)",
        "arg"
      )
    )
  }
}
