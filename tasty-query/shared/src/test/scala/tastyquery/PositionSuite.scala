package tastyquery

import scala.collection.mutable
import scala.concurrent.ExecutionContext.Implicits.global
import scala.reflect.TypeTest

import tastyquery.Names.*
import tastyquery.Trees.*
import tastyquery.Traversers.*

import tastyquery.TestUtils.*

class PositionSuite extends RestrictedUnpicklingSuite {
  def testUnpickle(name: String, rootSymbolPath: String)(using munit.Location)(body: Tree => Unit): Unit =
    testUnpickle(new munit.TestOptions(name), rootSymbolPath)(body)
  end testUnpickle

  def testUnpickle(testOptions: munit.TestOptions, rootSymbolPath: String)(
    using munit.Location
  )(body: Tree => Unit): Unit =
    test(testOptions) {
      for (base, tree) <- findTopLevelTasty(rootSymbolPath)() yield body(tree)
    }
  end testUnpickle

  private def posToCode(pos: SourcePosition): Option[String] =
    if !pos.isUnknown && !pos.isZeroExtent && pos.sourceFile.path.startsWith("test-sources/src/") then
      val relPath = pos.sourceFile.path.stripPrefix("test-sources/src/")
      val code = tastyquery.testutil.TestPlatform.readResourceCodeFile(relPath)
      Some(code.slice(pos.startOffset, pos.endOffset))
    else None
  end posToCode

  private def collectCode[T <: Tree](tree: Tree)(using tt: TypeTest[Tree, T]): List[String] =
    object collector extends TreeTraverser:
      val buffer = mutable.ListBuffer.empty[String]

      override def traverse(tree: Tree): Unit =
        tree match
          case tt(t: T) => buffer ++= posToCode(t.pos)
          case _        => ()
        super.traverse(tree)
    end collector

    collector.traverse(tree)

    collector.buffer.toList
  end collectCode

  /** Basics */

  testUnpickle("var-def", "simple_trees.Var") { tree =>
    assertEquals(collectCode[ValDef](tree), List("var x = 1"))
  }

  testUnpickle("literal", "simple_trees.Constants") { tree =>
    assertEquals(
      collectCode[Literal](tree),
      List("()", "false", "true", "1", "1", "'a'", "1", "1L", "1.5f", "1.1d", "\"string\"", "null")
    )
  }

  testUnpickle("assign", "simple_trees.Assign") { tree =>
    assertEquals(collectCode[Assign](tree), List("y = x"))
  }

  testUnpickle("apply", "simple_trees.EtaExpansion") { tree =>
    assertEquals(collectCode[Apply](tree), List("f(0)", "takesFunction(intMethod)", "intMethod"))
  }

  /** Control structures */

  testUnpickle("if", "simple_trees.If") { tree =>
    assertEquals(collectCode[If](tree), List("if (x < 0) -x else x"))
  }

  testUnpickle("while", "simple_trees.While") { tree =>
    assertEquals(
      collectCode[While](tree),
      List("""while (true) {
             |      ()
             |    }""".stripMargin)
    )

    val whilePos = findTree(tree) { case whileTree: While =>
      whileTree.pos
    }
    assert(clue(whilePos.startLine) == 4)
    assert(clue(whilePos.startColumn) == 4)
    assert(clue(whilePos.pointLine) == 4)
    assert(clue(whilePos.pointColumn) == 4)
    assert(clue(whilePos.endLine) == 6)
    assert(clue(whilePos.endColumn) == 5)
  }

  testUnpickle("match", "simple_trees.Match") { tree =>
    assertEquals(
      collectCode[Match](tree),
      List(
        """x match {
          |    case 0 => 0
          |    case 1 | -1 | 2 => x + 1
          |    case 7 if x == 7 => x - 1
          |    case 3 | 4 | 5 if x < 5 => 0
          |    case _ if (x % 2 == 0) => x / 2
          |    case _ => -x
          |  }""".stripMargin,
        """xs match
          |    case List(elems*) => 0
          |    case _            => 1""".stripMargin
      )
    )

    val matchPos = findTree(tree) { case matchTree @ Match(Ident(SimpleName("x")), _) =>
      matchTree.pos
    }
    assert(clue(matchPos.startLine) == 3)
    assert(clue(matchPos.startColumn) == 23)
    assert(clue(matchPos.pointLine) == 3)
    assert(clue(matchPos.pointColumn) == 25)
    assert(clue(matchPos.endLine) == 10)
    assert(clue(matchPos.endColumn) == 3)
  }

  testUnpickle("case-def", "simple_trees.Match") { tree =>
    assertEquals(
      collectCode[CaseDef](tree),
      List(
        "case 0 => 0",
        "case 1 | -1 | 2 => x + 1",
        "case 7 if x == 7 => x - 1",
        "case 3 | 4 | 5 if x < 5 => 0",
        "case _ if (x % 2 == 0) => x / 2",
        "case _ => -x",
        "case List(elems*) => 0",
        "case _            => 1"
      )
    )
  }

  testUnpickle("bind", "simple_trees.Bind") { tree =>
    assertEquals(collectCode[Bind](tree), List("t @ (y: Int)", "y: Int", "s: String", "k @ Some(_)"))
  }

  /** Functions */

  testUnpickle("def-def", "simple_trees.Function") { tree =>
    assertEquals(
      collectCode[DefDef](tree),
      List(
        "(x: Int) => x + 1",
        "() => ()",
        "T] => T => T", // TODO Improve this
        "[T] => (x: T) => x",
        "(x: Any) => x.type",
        "x => x"
      )
    )
  }

  testUnpickle("def-def-nested", "simple_trees.NestedMethod") { tree =>
    assertEquals(
      collectCode[DefDef](tree),
      List(
        """def outerMethod: Unit = {
          |    def innerMethod: Unit = ()
          |  }""".stripMargin,
        "def innerMethod: Unit = ()"
      )
    )
  }

  testUnpickle("named-arg", "simple_trees.NamedArgument") { tree =>
    assertEquals(collectCode[NamedArg](tree), List("second = 1"))
  }

  testUnpickle("block", "simple_trees.Block") { tree =>
    assertEquals(
      collectCode[Block](tree),
      List("""{
             |    val a = 1
             |    val b = 2
             |    ()
             |  }""".stripMargin)
    )
  }

  testUnpickle("lambda", "simple_trees.Function") { tree =>
    assertEquals(collectCode[Lambda](tree), List("(x: Int) => x + 1", "() => ()", "[T] => (x: T) => x", "x => x"))
  }

  testUnpickle("return", "simple_trees.Return") { tree =>
    assertEquals(collectCode[Return](tree), List("return 1"))
  }

  /** Classes */

  testUnpickle("class", "simple_trees.InnerClass") { tree =>
    assertEquals(
      collectCode[ClassDef](tree),
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

  testUnpickle("super", "simple_trees.Super") { tree =>
    assertEquals(
      collectCode[Super](tree),
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

  testUnpickle("class-with-self", "simple_trees.ClassWithSelf") { tree =>
    // ignore because the span of Self is impossible to construct
    assertEquals(collectCode[SelfDef](tree), Nil)
  }

  testUnpickle("trait-with-self", "simple_trees.TraitWithSelf") { tree =>
    // ignore because the span of Self is impossible to construct
    assertEquals(collectCode[SelfDef](tree), List("ClassWithSelf"))
  }

  /** Import and export */

  testUnpickle("import", "imports.Import") { tree =>
    assertEquals(collectCode[Import](tree), List("import imported_files.A"))
  }

  testUnpickle("import-selector-multiple", "imports.MultipleImports") { tree =>
    assertEquals(collectCode[ImportSelector](tree), List("A", "B"))
  }

  testUnpickle("import-selector-bound", "imports.ImportGivenWithBound") { tree =>
    assertEquals(collectCode[ImportSelector](tree), List("A", "given A"))
  }

  testUnpickle("import-selector-renamed", "imports.RenamedImport") { tree =>
    assertEquals(collectCode[ImportSelector](tree), List("A => ClassA", "ClassInSameFile as RenamedClassInSameFile"))
  }

  testUnpickle("export", "simple_trees.Export") { tree =>
    assertEquals(
      collectCode[Export](tree),
      List("export first.status", "export second.{status => _, *}", "export givens.given AnyRef")
    )
  }

  /** Throw and try-catch */

  testUnpickle("throw", "simple_trees.ThrowException") { tree =>
    assertEquals(collectCode[Throw](tree), List("throw new NullPointerException"))
  }

  testUnpickle("try", "simple_trees.TryCatch") { tree =>
    assertEquals(
      collectCode[Try](tree),
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

  testUnpickle("typed", "simple_trees.Typed") { tree =>
    assertEquals(collectCode[Typed](tree), List("1: Int"))
  }

  testUnpickle("type-member", "simple_trees.TypeMember") { tree =>
    assertEquals(
      collectCode[TypeMember](tree),
      List(
        "type TypeMember = Int",
        "type AbstractType",
        "type AbstractWithBounds >: Null <: Product",
        "opaque type Opaque = Int",
        "opaque type OpaqueWithBounds >: Null <: Product = Null"
      )
    )
  }

  testUnpickle("type-apply", "simple_trees.TypeApply") { tree =>
    assertEquals(collectCode[TypeApply](tree), List("Seq", "Seq[Int]", "A[Int, Seq[String]]"))
  }

  testUnpickle("type-ident", "simple_trees.Typed") { tree =>
    assertEquals(collectCode[TypeIdent](tree), List("Int"))
  }

  testUnpickle("singleton-type", "simple_trees.SingletonType") { tree =>
    assertEquals(collectCode[SingletonTypeTree](tree), List("x.type"))
  }

  testUnpickle("refined-type", "simple_trees.RefinedType") { tree =>
    assertEquals(collectCode[RefinedTypeTree](tree), List("{ def foo(using Int): Int }"))
  }

  testUnpickle("by-name-type", "simple_trees.ByNameParameter") { tree =>
    assertEquals(collectCode[ByNameTypeTree](tree), List("=> Int"))
  }

  testUnpickle("applied-type", "simple_trees.AppliedTypeAnnotation") { tree =>
    assertEquals(collectCode[AppliedTypeTree](tree), List("Option[Int]"))
  }

  testUnpickle("select-type", "simple_trees.SelectType") { tree =>
    assertEquals(collectCode[SelectTypeTree](tree), List("util.Random"))
  }

  testUnpickle("annotated-type", "simple_trees.VarargFunction") { tree =>
    assertEquals(collectCode[AnnotatedTypeTree](tree), List("Int*"))
  }

  testUnpickle("match-type", "simple_trees.MatchType") { tree =>
    assertEquals(
      collectCode[MatchTypeTree](tree),
      List(
        """X match {
          |    case Int => String
          |  }""".stripMargin,
        """Product = X match {
          |    case Int => Some[Int]""".stripMargin,
        """X match {
          |    case _ => Int
          |  }""".stripMargin,
        """X match {
          |    case List[t] => t
          |  }""".stripMargin
      )
    )
  }

  testUnpickle("type-tree-bind", "simple_trees.MatchType") { tree =>
    assertEquals(collectCode[TypeTreeBind](tree), List("t", "t"))
  }

  testUnpickle("named-type-bounds", "simple_trees.MatchType") { tree =>
    assertEquals(collectCode[NamedTypeBoundsTree](tree), List("t", "t"))
  }

  testUnpickle("type-definition-tree-1", "simple_trees.TypeMember") { tree =>
    assertEquals(
      collectCode[TypeDefinitionTree](tree),
      List(
        "Int",
        /* The following makes no sense; it is the position of the type def
         * of `type AbstractType`. It's probably dotc's auto-assigning of
         * positions that goes wild.
         */
        """type AbstractType
          |  type AbstractWithBounds >: Null <: Product""".stripMargin,
        ">: Null <: Product",
        "Int",
        "Null <: Product = Null",
        "Null <: Product"
      )
    )
  }

  testUnpickle("type-definition-tree-2", "simple_trees.TypeLambda") { tree =>
    assertEquals(
      collectCode[TypeDefinitionTree](tree),
      List(
        "[X] =>> List[X]",
        "X] =>> List[X]", // TODO Improve this
        "List[X]"
      )
    )
  }

  /** Inlined */

  testUnpickle("inlined", "simple_trees.InlinedCall") { tree =>
    assertEquals(collectCode[Inlined](tree), List("new withInlineMethod.Inner().inlined(0)", "arg"))
  }

  testUnpickle("shared-type", "simple_trees.SharedType") { tree =>
    assertEquals(collectCode[Ident](tree), List("println", "println"))
  }

}
