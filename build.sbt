import sbt.Keys.libraryDependencies

ThisBuild / scalaVersion := "3.0.0-RC2"
Test / parallelExecution := false

lazy val root =
  project.in(file(".")).aggregate(tastyQuery.js, tastyQuery.jvm).settings(publish := {}, publishLocal := {})

lazy val testSources = project.in(file("test-sources"))

lazy val tastyQuery =
  crossProject(JSPlatform, JVMPlatform)
    .in(file("."))
    .settings(
      name := "tasty-query",
      version := "0.1-SNAPSHOT",
    )
    .settings(
      libraryDependencies += "org.scala-lang" %% "tasty-core" % "3.0.0-RC2",
      libraryDependencies += "org.scalameta" %% "munit" % "0.7.23" % Test,
      testFrameworks += new TestFramework("munit.Framework")
    )
    .settings(javaOptions += {
      val testSourcesProducts = (testSources / Compile / products).value
      // Only one output location expected
      assert(testSourcesProducts.size == 1)
      "-Dtest-resources=" + testSourcesProducts.map(_.getAbsolutePath).head
    })
    .jvmSettings(fork := true)
    .jsSettings(scalaJSUseMainModuleInitializer := true)
