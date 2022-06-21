package tastyquery.testutil

import tastyquery.reader.classfiles.Classpaths.Classpath

transparent inline def testPlatform(using testPlatform: TestPlatform): testPlatform.type = testPlatform

trait TestPlatform {
  def loadClasspath(): Classpath
}
