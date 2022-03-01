import tastyquery.Contexts
import tastyquery.Contexts.FileContext
import tastyquery.ast.Trees.Tree
import tastyquery.reader.TastyUnpickler
import tastyquery.reader.PositionUnpickler

import java.nio.file.{Files, Paths}

class PositionSuite extends BaseUnpicklingSuite {

  override def unpickle(filename: String)(using ctx: FileContext = Contexts.empty(filename)): Tree = {
    val resourcePath = getResourcePath(filename)
    val bytes = Files.readAllBytes(Paths.get(resourcePath))
    val unpickler = new TastyUnpickler(bytes)
    unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler(
        unpickler.unpickle(new TastyUnpickler.PositionSectionUnpickler))).get.unpickle(using ctx).head
  }

  test("empty-class") {
    val tree = unpickle("empty_class/EmptyClass")
    tree.walkTree(t => println(t.span))
  }

  test("nested-package") {
    val tree = unpickle("simple_trees/nested/InNestedPackage")
    tree.walkTree(t => println(t.span))
  }

  test("qualified-nested-package") {
    val tree = unpickle("simple_trees/nested/InQualifiedNestedPackage")
    tree.walkTree(t => println(t.span))
  }
}