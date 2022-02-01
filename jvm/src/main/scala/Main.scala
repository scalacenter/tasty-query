import java.nio.file.{Files, Paths}
import tastyquery.reader.TastyUnpickler
import tastyquery.Contexts
import tastyquery.api.ProjectReader

import java.net.URL
import java.net.URLClassLoader

object Main {
  def main(args: Array[String]): Unit =
    args.toList match {
      case "-cp" :: classpath =>
        val reader = new ProjectReader
        reader.read(classpath)
      case _ =>
        println("""Usage:
                  |-cp <path: String>[ <path: String>[ <path: String>...]]""".stripMargin)
    }
}
