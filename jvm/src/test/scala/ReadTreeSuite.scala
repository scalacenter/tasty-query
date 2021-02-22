import tastyquery.ast.Trees.Tree
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

  // TODO: add structure checks on the unpickling result
  def checkUnpickle(name: String): Unit =
    test(name) {
      val resourcePath = getResourcePath(name)
      val bytes = Files.readAllBytes(Paths.get(resourcePath))
      unpickle(bytes)
    }

  checkUnpickle("EmptyClass")
}
