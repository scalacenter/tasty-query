package tastyquery

import java.nio.file.{Files, Paths}
import tastyquery.reader.TastyUnpickler
import tastyquery.Contexts
import tastyquery.api.ProjectReader
import tastyquery.jdk.ClasspathLoaders

import java.net.URL
import java.net.URLClassLoader
import tastyquery.Contexts.BaseContext

object Main {
  def main(args: Array[String]): Unit =
    args.toList match {
      case "-cp" :: cp :: classes =>
        val reader = new ProjectReader
        val cpElems = ClasspathLoaders.splitClasspath(cp)
        val classpath = ClasspathLoaders.read(cpElems, Set(ClasspathLoaders.FileKind.Tasty))
        given BaseContext = Contexts.init(classpath)
        reader.read(classes*).debugDefinitions
      case _ =>
        println("""Usage:
                  |-cp <paths> <classname>...""".stripMargin)
    }
}
