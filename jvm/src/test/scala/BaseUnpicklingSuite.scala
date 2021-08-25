import tastyquery.Contexts
import tastyquery.Contexts.Context
import tastyquery.ast.Trees.Tree
import tastyquery.ast.Types.Type
import tastyquery.reader.TastyUnpickler

import java.nio.file.{Files, Paths}

abstract class BaseUnpicklingSuite extends munit.FunSuite {
  val ResourceProperty = "test-resources"

  def unpickle(filename: String)(using ctx: Context = Contexts.empty): Tree = {
    val resourcePath = getResourcePath(filename)
    val bytes        = Files.readAllBytes(Paths.get(resourcePath))
    val unpickler    = new TastyUnpickler(bytes)
    unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler()).get.unpickle (using ctx).head
  }

  def getResourcePath(name: String): String =
    s"${System.getProperty(ResourceProperty)}/$name.tasty"
}
