package examples

import java.nio.file.*

import tastyquery.Classpaths.*
import tastyquery.Contexts
import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.jdk.ClasspathLoaders

object TastyPrint:
  private val TestClassPathEnvVar = "TASTY_TEST_CLASSPATH"

  def main(args: Array[String]): Unit =
    args.toList match {
      case classes if classes.nonEmpty =>
        val classpath = loadClasspath()
        val ctx = Contexts.init(classpath)
        printTreesOf(classes)(using ctx)
      case _ =>
        println("""Usage:
                  |examples.TastyPrint <classname>...""".stripMargin)
    }
  end main

  private def loadClasspath(): Classpath =
    val stringEntries = System.getenv(TestClassPathEnvVar).nn.split(';').toList

    val entries: List[Path] =
      for stringEntry <- stringEntries yield stringEntry match
        case s"jrt:/modules/$module/" =>
          FileSystems.getFileSystem(java.net.URI.create("jrt:/")).nn.getPath("modules", module).nn
        case _ =>
          Paths.get(stringEntry).nn

    ClasspathLoaders.read(entries)
  end loadClasspath

  private def printTreesOf(classes: List[String])(using Context): Unit =
    printTrees(getTreesOf(classes))
  end printTreesOf

  private def getTreesOf(classes: List[String])(using Context): List[Tree] =
    for className <- classes yield
      val parts = className.split('.').toList
      val path = parts.init.map(termName(_)) :+ typeName(parts.last)
      val classSym = ctx.findSymbolFromRoot(path)
      val defTree: DefTree = classSym.tree.getOrElse {
        throw IllegalArgumentException(s"Cannot find TASTy tree for $className")
      }
      defTree.asInstanceOf[Tree]
  end getTreesOf

  private def printTrees(trees: List[Tree]): Unit =
    for tree <- trees do
      tree.walkTree {
        case ddef: DefTree =>
          println(ddef.symbol.fullName.toDebugString)
        case _ =>
      }
  end printTrees
end TastyPrint
