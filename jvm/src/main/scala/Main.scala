import java.nio.file.{Files, Paths}
import tastyquery.reader.TastyUnpickler
import tastyquery.Contexts
import tastyquery.api.ProjectReader

import java.net.URL
import java.net.URLClassLoader

object Main {
  def main(args: Array[String]): Unit =
    args.toList match {
      case Nil =>
        // By default, read this project
        val cl = ClassLoader.getSystemClassLoader
        val classpath = cl.asInstanceOf[URLClassLoader].getURLs.map(_.getFile).toList
        val reader = new ProjectReader
        reader.read(classpath)
      case "-cp" :: classpath =>
        val reader = new ProjectReader
        reader.read(classpath)
      case "--standalone" :: filename :: Nil =>
        val unpickler = new TastyUnpickler(Files.readAllBytes(Paths.get(filename)))
        println(
          unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler()).get.unpickle(using Contexts.empty(filename))
        )
      case _ =>
        println("""Two modes of usage:
                  |--standalone tasty-file
                  |-cp whitespace-separated-classpath-entries
                  |By default, will read the current project.""".stripMargin)
    }
}
