import tastyquery.Contexts
import tastyquery.Contexts.FileContext
import tastyquery.ast.Trees._
import tastyquery.reader.TastyUnpickler
import tastyquery.reader.PositionUnpickler
import dotty.tools.dotc.util.Spans.{Span, NoSpan}

import scala.reflect.TypeTest
import java.nio.file.{Files, Paths}

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

  test("var") {
    val (tree, code) = unpickleWithCode("simple_trees/Var")
    assertEquals(
      collectCode[ValDef](tree, code),
      List("var x = 1")
    )
  }

  test("constants") {
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

  test("if") {
    val (tree, code) = unpickleWithCode("simple_trees/If")
    assertEquals(
      collectCode[If](tree, code),
      List("if (x < 0) -x else x")
    )
  }

  test("function") {
    val (tree, code) = unpickleWithCode("simple_trees/Function")
    assertEquals(
      collectCode[DefDef](tree, code),
      List(
        "(x: Int) => x + 1",
        "() => ()"
      )
    )
  }

  // test("inlined-call") {
  //   val tree = unpickle("simple_trees/InlinedCall")
  // }

  test("return") {
    val (tree, code) = unpickleWithCode("simple_trees/Return")
    assertEquals(
      collectCode[Return](tree, code),
      List("return 1")
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

  test("CaseDef") {
    val (tree, code) = unpickleWithCode("simple_trees/Match")
    assertEquals(
      collectCode[CaseDef](tree, code), 
      Nil
    )
  }

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

}
