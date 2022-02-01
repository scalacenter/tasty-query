package tastyquery.api

import org.apache.commons.io.{FileUtils, IOUtils}
import tastyquery.Contexts
import tastyquery.ast.Trees.Tree
import tastyquery.reader.{TastyUnpickler, TreeUnpickler}

import java.io.{File, InputStream}
import java.nio.file.{Files, Paths}
import java.util.jar.JarFile
import scala.jdk.CollectionConverters.*

class ProjectReader {

  def read(classpath: List[String]): TastyQuery = {
    val unpicklingCtx = Contexts.empty
    val trees = classpathToEntries(classpath).flatMap(
      _.walkTastyFiles((filename, stream) => getTreeUnpickler(stream).unpickle(using unpicklingCtx.withFile(filename)))
    )
    new TastyQuery(unpicklingCtx, TastyTrees(trees))
  }

  private def getTreeUnpickler(fileStream: InputStream): TreeUnpickler = {
    val bytes = {
      import scala.language.unsafeNulls
      IOUtils.toByteArray(fileStream)
    }
    val unpickler = new TastyUnpickler(bytes)
    unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler()).get
  }

  private def classpathToEntries(classpath: List[String]): List[ClasspathEntry] =
    classpath.map(e =>
      if (Files.exists(Paths.get(e))) {
        if (e.endsWith(".jar")) Jar(e)
        else if (Files.isDirectory(Paths.get(e))) Directory(e)
        else InvalidEntry(e)
      } else {
        InvalidEntry(e)
      }
    )
}

sealed abstract class ClasspathEntry(val path: String) {
  def walkTastyFiles(op: (String, InputStream) => List[Tree]): List[Tree]
}

final case class Jar(override val path: String) extends ClasspathEntry(path) {
  def getFullPath(filename: String): String = s"$path:$filename"

  override def walkTastyFiles(op: (String, InputStream) => List[Tree]): List[Tree] = {
    val jar = JarFile(path)
    // TODO: a nicer way to force?
    import scala.language.unsafeNulls
    val stream = jar.stream()
    // force the execution of filter + map on the stream:
    stream
      .iterator()
      .asScala
      .filter { je =>
        val name = je.getName
        name.endsWith(".tasty")
      }
      .flatMap(je => op(getFullPath(je.getName()), jar.getInputStream(je)))
      .toList
  }
}

final case class Directory(override val path: String) extends ClasspathEntry(path) {
  override def walkTastyFiles(op: (String, InputStream) => List[Tree]): List[Tree] = {
    import scala.language.unsafeNulls
    FileUtils
      .listFiles(new File(path), Array("tasty"), true)
      .asScala
      .flatMap(f => op(f.getAbsolutePath(), FileUtils.openInputStream(f)))
      .toList
  }
}

final case class InvalidEntry(override val path: String) extends ClasspathEntry(path) {
  override def walkTastyFiles(op: (String, InputStream) => List[Tree]): List[Tree] = Nil
}
