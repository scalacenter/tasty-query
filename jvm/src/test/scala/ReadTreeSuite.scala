import tastyquery.ast.Names.{SimpleName, QualifiedName, TypeName}
import tastyquery.ast.Trees._
import tastyquery.ast.Types.{TermRef, TypeRef}
import tastyquery.reader.TastyUnpickler

import java.nio.file.{Files, Paths}

class ReadTreeSuite extends munit.FunSuite {
  val ResourceProperty = "test-resources"

  def unpickle(tastyBytes: Array[Byte]): List[Tree] = {
    val unpickler = new TastyUnpickler(tastyBytes)
    unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler()).get.unpickle
  }

  def getResourcePath(name: String): String =
    s"${System.getProperty(ResourceProperty)}/$name.tasty"

  def checkUnpickle(name: String, p: PartialFunction[Tree, Unit]): Unit =
    test(name) {
      val resourcePath = getResourcePath(name)
      val bytes = Files.readAllBytes(Paths.get(resourcePath))
      val tree = unpickle(bytes).head
      assert(p.isDefinedAt(tree))
    }

  val isJavaLangObject: PartialFunction[Tree, Unit] = {
    case Apply(Select(
    New(TypeTree(TypeRef(
    TermRef(_, QualifiedName(_, SimpleName("java"), SimpleName("lang"))),
    TypeName(SimpleName("Object"))))),
    _), List()) =>
  }

  checkUnpickle("EmptyClass", {
    case PackageDef(_, List(
    TypeDef(TypeName(SimpleName("EmptyClass")),
    Template(
    // default constructor: no type params, no arguments, empty body
    DefDef(SimpleName("<init>"), List(), List(), TypeTree(_), EmptyTree),
    // a single parent -- java.lang.Object
    List(parent),
    // self not specified => EmptyValDef
    EmptyValDef,
    // empty body
    List()
    )))
    ) if isJavaLangObject.isDefinedAt(parent) =>
  })
}
