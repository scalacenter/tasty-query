import java.nio.file.{Files, Paths}

import tastyquery.reader.TastyUnpickler
import tastyquery.Contexts

object Main {
  def main(args: Array[String]): Unit =
    if (args.isEmpty) {
      println("Please enter a tasty file to read")
    } else {
      val filename  = args(0)
      val unpickler = new TastyUnpickler(Files.readAllBytes(Paths.get(filename)))
      println(unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler()).get.unpickle (using Contexts.empty))
    }
}
