import tastyquery.ast.Names.{SimpleName, QualifiedName, TypeName}
import tastyquery.ast.Trees._
import tastyquery.ast.Types.{TermRef, TypeRef}
import tastyquery.reader.TastyUnpickler

import java.nio.file.{Files, Paths}

class ReadTreeSuite extends munit.FunSuite {
  val ResourceProperty = "test-resources"

  def unpickle(filename: String): Tree = {
    val resourcePath = getResourcePath(filename)
    val bytes        = Files.readAllBytes(Paths.get(resourcePath))
    val unpickler    = new TastyUnpickler(bytes)
    unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler()).get.unpickle.head
  }

  def getResourcePath(name: String): String =
    s"${System.getProperty(ResourceProperty)}/$name.tasty"

  val isJavaLangObject: PartialFunction[Tree, Unit] = {
    case Apply(
          Select(
            New(
              TypeTree(
                TypeRef(
                  TermRef(_, QualifiedName(_, SimpleName("java"), SimpleName("lang"))),
                  TypeName(SimpleName("Object"))
                )
              )
            ),
            _
          ),
          List()
        ) =>
  }

  test("empty-class") {
    assert(clue({
      {
        case PackageDef(
              _,
              List(
                TypeDef(
                  TypeName(SimpleName("EmptyClass")),
                  Template(
                    // default constructor: no type params, no arguments, empty body
                    DefDef(SimpleName("<init>"), List(), List(), TypeTree(_), EmptyTree),
                    // a single parent -- java.lang.Object
                    List(parent),
                    // self not specified => EmptyValDef
                    EmptyValDef,
                    // empty body
                    List()
                  )
                )
              )
            ) if isJavaLangObject.isDefinedAt(parent) =>
      }: PartialFunction[Tree, Unit]
    }).isDefinedAt(clue(unpickle("empty_class/EmptyClass"))))
  }
}
