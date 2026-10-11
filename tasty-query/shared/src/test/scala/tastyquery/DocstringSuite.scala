package tastyquery

import scala.concurrent.ExecutionContext.Implicits.global

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Symbols.*

import TestUtils.*

class DocstringSuite extends UnrestrictedUnpicklingSuite {
  def assertDocString(sym: Symbol, expected: String)(using munit.Location): Unit =
    assertEquals(sym.docComment.map(_.raw), Some(expected), sym.toString)

  def assertNoDocString(sym: Symbol)(using munit.Location): Unit =
    assertEquals(sym.docComment, None, sym.toString)

  def assertDocCommentPositionMatchesText(sym: Symbol)(using munit.Location): Unit =
    val docComment = sym.docComment.get
    val sourceFile = sym.tree.get.pos.sourceFile
    val relPath = sourceFile.path.stripPrefix("test-sources/src/")
    val code = tastyquery.testutil.TestPlatform.readResourceCodeFile(relPath)
    assertEquals(code.slice(docComment.startOffset, docComment.endOffset), docComment.raw)

  testWithContext("class-and-members") {
    val Docstrings = ctx.findTopLevelClass("simple_trees.Docstrings")

    assertDocString(
      Docstrings,
      """/** Doc of class Docstrings.
        |  *
        |  * @param ctorParam doc of ctorParam
        |  */""".stripMargin
    )

    assertDocString(Docstrings.findNonOverloadedDecl(name"method"), "/** Doc of method. */")
    assertDocString(Docstrings.findDecl(name"value"), "/** Doc of value. */")
    assertDocString(Docstrings.findDecl(name"variable"), "/** Doc of variable. */")
    assertDocString(Docstrings.findNonOverloadedDecl(name"variable_="), "/** Doc of variable. */")
    assertDocString(Docstrings.findDecl(name"lazyValue"), "/** Doc of lazy value. */")
    assertDocString(Docstrings.findDecl(tname"TypeMember"), "/** Doc of type member. */")
    assertDocString(Docstrings.findDecl(tname"AbstractTypeMember"), "/** Doc of abstract type member. */")
    assertDocString(Docstrings.findDecl(tname"NestedClass"), "/** Doc of nested class. */")
    assertDocString(Docstrings.findDecl(name"NestedObject"), "/** Doc of nested object. */")
    assertDocString(Docstrings.findDecl(moduleClassName("NestedObject")), "/** Doc of nested object. */")
    assertDocString(Docstrings.findDecl(name"given_Ordering_Docstrings"), "/** Doc of given. */")
    assertDocString(Docstrings.findDecl(name"withLocal"), "/** Doc of local. */")

    assertNoDocString(Docstrings.findDecl(name"undocumented"))
    assertNoDocString(Docstrings.findDecl(name"ctorParam"))
    assertNoDocString(Docstrings.typeParams.head)

    val method = Docstrings.findNonOverloadedDecl(name"method")
    assertNoDocString(method.paramSymss.head.left.toOption.get.head)

    val ctors = Docstrings.findAllOverloadedDecls(nme.Constructor)
    assertEquals(ctors.map(_.docComment.map(_.raw)).toSet, Set(None, Some("/** Doc of secondary constructor. */")))
  }

  testWithContext("positions") {
    val Docstrings = ctx.findTopLevelClass("simple_trees.Docstrings")
    assertDocCommentPositionMatchesText(Docstrings)
    assertDocCommentPositionMatchesText(Docstrings.findNonOverloadedDecl(name"method"))
    assertDocCommentPositionMatchesText(Docstrings.findDecl(tname"NestedClass"))
    assertDocCommentPositionMatchesText(ctx.findTopLevelModuleClass("simple_trees.Docstrings"))

    val classDoc = Docstrings.docComment.get
    val classDef = Docstrings.tree.get.pos
    assert(classDoc.endOffset <= classDef.startOffset, clue((classDoc, classDef)))
  }

  testWithContext("companion-object") {
    val DocstringsModule = ctx.findTopLevelModuleClass("simple_trees.Docstrings")
    assertDocString(DocstringsModule, "/** Doc of object Docstrings. */")
    assertDocString(DocstringsModule.moduleValue.get, "/** Doc of object Docstrings. */")
    assertDocString(DocstringsModule.findDecl(name"objectMember"), "/** Doc of object member. */")
  }

  testWithContext("trait-enum-standalone-object") {
    assertDocString(ctx.findTopLevelClass("simple_trees.DocstringsTrait"), "/** Doc of trait. */")

    val DocstringsEnum = ctx.findTopLevelClass("simple_trees.DocstringsEnum")
    assertDocString(DocstringsEnum, "/** Doc of enum. */")
    val DocstringsEnumModule = ctx.findTopLevelModuleClass("simple_trees.DocstringsEnum")
    assertDocString(DocstringsEnumModule.findDecl(name"Case1"), "/** Doc of enum case. */")
    assertDocString(DocstringsEnumModule.findDecl(tname"Case2"), "/** Doc of parameterized enum case. */")
    assertDocString(DocstringsEnumModule, "/** Doc of enum. */")
    assertDocString(
      DocstringsEnumModule.findNonOverloadedDecl(name"fromOrdinal"),
      "/** Doc of parameterized enum case. */"
    )

    assertDocString(
      ctx.findTopLevelModuleClass("simple_trees.DocstringsStandaloneObject"),
      "/** Doc of standalone object. */"
    )
  }

  testWithContext("no-docstrings-outside-tasty") {
    val JavaDefined = ctx.findTopLevelClass("javadefined.JavaDefined")
    assertNoDocString(JavaDefined)
    for decl <- JavaDefined.declarations do assertNoDocString(decl)

    val MacrosClass = ctx.findTopLevelModuleClass("scalatwo.Macros")
    assertNoDocString(MacrosClass)
    for decl <- MacrosClass.declarations do assertNoDocString(decl)

    assertNoDocString(ctx.findPackage("javadefined"))
  }

  testWithContext("non-ascii") {
    val Docstrings = ctx.findTopLevelClass("simple_trees.Docstrings")
    val nonAscii = Docstrings.findDecl(name"nonAscii")
    assertDocString(nonAscii, "/** Doc with non-ASCII: café — ünïcödé ✓ 日本語 */")
    assertDocCommentPositionMatchesText(nonAscii)
  }

  testWithContext("case-class") {
    val DocstringsCaseClass = ctx.findTopLevelClass("simple_trees.DocstringsCaseClass")
    assertDocString(DocstringsCaseClass, "/** Doc of case class. */")
    assertNoDocString(DocstringsCaseClass.findDecl(name"x"))
    assertNoDocString(DocstringsCaseClass.findNonOverloadedDecl(name"copy"))
    assertNoDocString(DocstringsCaseClass.findNonOverloadedDecl(name"_1"))

    val DocstringsCaseClassModule = ctx.findTopLevelModuleClass("simple_trees.DocstringsCaseClass")
    assertDocString(DocstringsCaseClassModule, "/** Doc of case class. */")
    assertDocString(DocstringsCaseClassModule.moduleValue.get, "/** Doc of case class. */")
    assertNoDocString(DocstringsCaseClassModule.findNonOverloadedDecl(name"apply"))
    assertNoDocString(DocstringsCaseClassModule.findNonOverloadedDecl(name"unapply"))
  }

  testWithContext("top-level-definitions") {
    val packageObject = ctx.findTopLevelModuleClass("simple_trees.DocstringsTopLevel$package")
    assertNoDocString(packageObject)
    assertDocString(packageObject.findDecl(name"docstringsTopLevelDef"), "/** Doc of top-level def. */")
    assertDocString(packageObject.findDecl(name"docstringsTopLevelVal"), "/** Doc of top-level val. */")
  }

  testWithContext("local-definition") {
    val Docstrings = ctx.findTopLevelClass("simple_trees.Docstrings")
    val withLocal = Docstrings.findNonOverloadedDecl(name"withLocal")
    val local = findLocalValDef(withLocal.tree.get, name"local")
    assertDocString(local, "/** Doc of local value. */")
  }

  testWithContext("scala-3-standard-library") {
    val ListClass = ctx.findTopLevelClass("scala.collection.immutable.List")
    assert(ListClass.docComment.exists(_.raw.startsWith("/**")), clue(ListClass.docComment))
  }
}
