package tastyquery.testutil.jdk

import tastyquery.testutil.TestPlatform
import java.nio.file.Files
import java.nio.file.Paths
import tastyquery.reader.classfiles.Classpaths.Classpath
import scala.util.Properties
import tastyquery.jdk.ClasspathLoaders
import java.io.File

object JavaTestPlatform extends TestPlatform {
  private val ResourceProperty = "test-resources"
  private val StdLibProperty = "std-library"

  private def resourcesDir = Properties.propOrNone(ResourceProperty).get
  private def stdLibPaths = {
    import scala.language.unsafeNulls
    Properties.propOrEmpty(StdLibProperty).split(File.pathSeparator).toList
  }

  def loadClasspath(includeClasses: Boolean, includeStdLib: Boolean): Classpath = {
    val parts0 = resourcesDir :: Nil
    val kinds0 = Set(ClasspathLoaders.FileKind.Tasty)
    val kinds = if includeClasses then kinds0 + ClasspathLoaders.FileKind.Class else kinds0
    val parts = if includeStdLib then parts0 ::: stdLibPaths else parts0
    ClasspathLoaders.read(parts, kinds)
  }
}
