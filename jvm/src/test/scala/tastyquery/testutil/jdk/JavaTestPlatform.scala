package tastyquery.testutil.jdk

import java.nio.file.*

import tastyquery.jdk.ClasspathLoaders
import tastyquery.reader.classfiles.Classpaths.Classpath
import tastyquery.testutil.TestPlatform

object JavaTestPlatform extends TestPlatform {
  private val TestClassPathEnvVar = "TASTY_TEST_CLASSPATH"

  private lazy val classpath: Classpath =
    val stringEntries = System.getenv(TestClassPathEnvVar).nn.split(';').toList

    val entries: List[Path] =
      for stringEntry <- stringEntries yield stringEntry match
        case s"jrt:/modules/$module/" =>
          FileSystems.getFileSystem(java.net.URI.create("jrt:/")).nn.getPath("modules", module).nn
        case _ =>
          Paths.get(stringEntry).nn

    ClasspathLoaders.read(entries)
  end classpath

  def loadClasspath(): Classpath =
    classpath
}
