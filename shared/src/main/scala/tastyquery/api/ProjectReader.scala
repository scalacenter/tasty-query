package tastyquery.api

import tastyquery.Contexts
import tastyquery.reader.{TastyUnpickler, TreeUnpickler}
import tastyquery.ast.Trees.Tree

import scala.jdk.CollectionConverters.*
import java.io.{File, InputStream}
import java.util.jar.JarFile
import org.apache.commons.io.IOUtils
import org.apache.commons.io.FileUtils

class ProjectReader {
  def read(classpath: List[String]): TastyQuery = {
    val unpicklingCtx = Contexts.empty
    val trees = classpathToEntries(classpath).flatMap(
      _.walkTastyFiles((filename, stream) => getTreeUnpickler(stream).unpickle(using unpicklingCtx.withFile(filename)))
    )
    new TastyQuery(unpicklingCtx, TastyTrees(trees))
  }

  private def getTreeUnpickler(fileStream: InputStream): TreeUnpickler = {
    val unpickler = new TastyUnpickler(IOUtils.toByteArray(fileStream))
    unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler()).get
  }

  private def classpathToEntries(classpath: List[String]): List[ClasspathEntry] =
    // TODO: check isdir
    classpath.map(e => if (e.endsWith(".jar")) Jar(e) else Directory(e))
}

sealed abstract class ClasspathEntry(val path: String) {
  def walkTastyFiles(op: (String, InputStream) => List[Tree]): List[Tree]
}

final case class Jar(override val path: String) extends ClasspathEntry(path) {
  def getFullPath(filename: String): String = s"$path:$filename"

  override def walkTastyFiles(op: (String, InputStream) => List[Tree]): List[Tree] = {
    val jar = JarFile(path)
    // TODO: a nicer way to force?
    jar
      .stream()
      // force the execution of filter + map on the stream:
      .iterator()
      .asScala
      .filter(je => je.getName().endsWith(".tasty"))
      .flatMap(je => op(getFullPath(je.getName()), jar.getInputStream(je)))
      .toList
  }
}

final case class Directory(override val path: String) extends ClasspathEntry(path) {
  override def walkTastyFiles(op: (String, InputStream) => List[Tree]): List[Tree] =
    FileUtils
      .listFiles(new File(path), Array("tasty"), true)
      .asScala
      .flatMap(f => op(f.getAbsolutePath(), FileUtils.openInputStream(f)))
      .toList
}
