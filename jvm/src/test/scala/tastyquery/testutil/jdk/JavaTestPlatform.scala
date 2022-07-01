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

  def loadClasspath(): Classpath = {
    val kinds = Set(ClasspathLoaders.FileKind.Tasty, ClasspathLoaders.FileKind.Class)
    val parts = resourcesDir :: stdLibPaths
    ClasspathLoaders.read(parts, kinds)
  }
}
