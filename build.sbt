import sbt.Keys.libraryDependencies

val usedScalaCompiler = "3.1.0"
val usedScala2StdLib = "2.13.7"
val usedTastyRelease = usedScalaCompiler

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
      libraryDependencies += "org.scala-lang" %% "tasty-core" % usedTastyRelease, // TODO: publish for JS or shade?
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
      libraryDependencies += "commons-io" % "commons-io" % "2.11.0",
      Test / javalibEntry := (Test / rtJarOpt).value.getOrElse("jrt:/modules/java.base/"),
    )
    .jsSettings(
      scalaJSUseMainModuleInitializer := true,
      scalaJSLinkerConfig ~= (_.withModuleKind(ModuleKind.ESModule)),
      Test / javalibEntry := (Test / rtJarOpt).value.getOrElse("jrt:/modules/java.base/"), // TODO
    )
