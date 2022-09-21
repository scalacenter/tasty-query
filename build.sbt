import sbt.Keys.libraryDependencies

val usedScalaCompiler = "3.1.0"
val usedScala2StdLib = "2.13.7"
val usedTastyRelease = usedScalaCompiler

val SourceDeps = config("sourcedeps").hide

val rtJarOpt = taskKey[Option[String]]("Path to rt.jar if it exists")
val javalibEntry = taskKey[String]("Path to rt.jar or \"jrt:/\"")

val commonSettings = Seq(
  scalaVersion := usedScalaCompiler,
  Test / parallelExecution := false
)

val strictCompileSettings = Seq(
  scalacOptions ++= Seq("-Yexplicit-nulls", "-Ysafe-init", "-source:future"),
)

lazy val root = project.in(file("."))
  .aggregate(tastyQuery.js, tastyQuery.jvm).settings(publish := {}, publishLocal := {})

lazy val testSources = project.in(file("test-sources"))
  .settings(commonSettings)

lazy val tastyQuery =
  crossProject(JSPlatform, JVMPlatform).in(file("."))
    .settings(commonSettings)
    .settings(strictCompileSettings)
    .settings(name := "tasty-query", version := "0.1-SNAPSHOT")
    .settings(
      libraryDependencies += "org.scalameta" %%% "munit" % "0.7.29" % Test,
      testFrameworks += new TestFramework("munit.Framework")
    )
    .settings(
      Test / rtJarOpt := {
        for (bootClasspath <- Option(System.getProperty("sun.boot.class.path"))) yield {
          val rtJarOpt = bootClasspath.split(java.io.File.pathSeparatorChar).find { path =>
            new java.io.File(path).getName() == "rt.jar"
          }
          rtJarOpt match {
            case Some(rtJar) =>
              rtJar
            case None =>
              throw new AssertionError(s"cannot find rt.jar in $bootClasspath")
          }
        }
      },

      Test / envVars ++= {
        val javalib = (Test / javalibEntry).value
        val testSourcesCP = Attributed.data((testSources / Compile / fullClasspath).value)
        val testClasspath = (javalib +: testSourcesCP.map(_.getAbsolutePath())).mkString(";")

        val testResourcesCode = (testSources / sourceDirectory).value.getAbsolutePath()

        Map(
          "TASTY_TEST_CLASSPATH" -> testClasspath,
          "TASTY_TEST_SOURCES" -> testResourcesCode,
        )
      }
    )
    .jvmSettings(
      fork := true,
      libraryDependencies += "org.scala-lang" %% "tasty-core" % usedTastyRelease,
      libraryDependencies += "commons-io" % "commons-io" % "2.11.0",
      Test / javalibEntry := (Test / rtJarOpt).value.getOrElse("jrt:/modules/java.base/"),
    )
    .jsSettings(
      // Add the sources of tasty-core, since it is not published for Scala.js
      ivyConfigurations += SourceDeps.hide,
      transitiveClassifiers := Seq("sources"),
      libraryDependencies += "org.scala-lang" %% "tasty-core" % usedTastyRelease % SourceDeps,
      (Compile / sourceGenerators) += Def.task {
        val s = streams.value
        val cacheDir = s.cacheDirectory
        val trgDir = (Compile / sourceManaged).value / "tasty-core-src"

        val report = updateClassifiers.value
        val tastyCoreSourcesJar = report.select(
            configuration = configurationFilter(SourceDeps.name),
            module = (_: ModuleID).name.startsWith("tasty-core_"),
            artifact = artifactFilter(`type` = "src")).headOption.getOrElse {
          throw new MessageOnlyException(s"Could not fetch tasty-core sources")
        }

        FileFunction.cached(cacheDir / s"fetchTastyCoreSource",
            FilesInfo.lastModified, FilesInfo.exists) { dependencies =>
          s.log.info(s"Unpacking tasty-core sources to $trgDir...")
          if (trgDir.exists)
            IO.delete(trgDir)
          IO.createDirectory(trgDir)
          IO.unzip(tastyCoreSourcesJar, trgDir)
          val sourceFiles = (trgDir ** "*.scala").get.toSet
          for (f <- sourceFiles)
            IO.writeLines(f, patchTastyCoreSource(IO.readLines(f)))
          sourceFiles
        } (Set(tastyCoreSourcesJar)).toSeq
      }.taskValue,

      scalaJSUseMainModuleInitializer := true,
      scalaJSLinkerConfig ~= (_.withModuleKind(ModuleKind.ESModule)),
      Test / javalibEntry := (Test / rtJarOpt).value.getOrElse("jrt:/modules/java.base/"), // TODO
    )

def patchTastyCoreSource(lines: List[String]): List[String] = {
  val importStatement = raw"""(?s)(^ *import .+\.)_$$""".r
  for (line <- lines) yield {
    line match {
      case importStatement(allButUnderscore) => allButUnderscore + "*"
      case _                                 => line
    }
  }
}
