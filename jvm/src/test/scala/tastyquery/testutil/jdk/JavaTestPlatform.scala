package tastyquery.testutil.jdk

import tastyquery.testutil.TestPlatform
import java.nio.file.Files
import java.nio.file.Paths
import tastyquery.reader.classfiles.Classpaths.Classpath
import scala.util.Properties
import tastyquery.jdk.ClasspathLoaders

object JavaTestPlatform extends TestPlatform {
  private val ResourceProperty = "test-resources"

  def loadClasspath(includeClasses: Boolean): Classpath = {
    val Some(resourcesDir) = Properties.propOrNone(ResourceProperty)
    val kinds0 = Set(ClasspathLoaders.FileKind.Tasty)
    val kinds = if includeClasses then kinds0 + ClasspathLoaders.FileKind.Class else kinds0
    ClasspathLoaders.read(resourcesDir :: Nil, kinds)
  }
}
