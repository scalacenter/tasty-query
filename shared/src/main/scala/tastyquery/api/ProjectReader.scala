package tastyquery.api

import tastyquery.Contexts
import tastyquery.reader.{TastyUnpickler, TreeUnpickler}

import scala.jdk.CollectionConverters.*
import java.io.{File, InputStream}
import java.util.jar.JarFile
import org.apache.commons.io.IOUtils
import org.apache.commons.io.FileUtils

class ProjectReader {
  def read(classpath: List[String]): TastyQuery = {
    val unpicklingCtx = Contexts.empty
    classpathToEntries(classpath).map(
      _.walkTastyFiles(stream => getTreeUnpickler(stream).unpickle(using unpicklingCtx))
    )
    new TastyQuery(unpicklingCtx)
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
  def walkTastyFiles(op: InputStream => Unit): Unit
}

final case class Jar(override val path: String) extends ClasspathEntry(path) {
  override def walkTastyFiles(op: InputStream => Unit): Unit = {
    val jar = JarFile(path)
    // TODO: a nicer way to force?
    jar
      .stream()
      // force the execution of filter + map on the stream:
      .iterator()
      .asScala
      .toList
      .filter(je => je.getName().endsWith(".tasty"))
      .map(je => op(jar.getInputStream(je)))
  }
}

final case class Directory(override val path: String) extends ClasspathEntry(path) {
  override def walkTastyFiles(op: InputStream => Unit): Unit =
    FileUtils
      .listFiles(new File(path), Array("tasty"), true)
      .asScala
      .map(f => op(FileUtils.openInputStream(f)))
}
