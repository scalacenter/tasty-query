import sbt.Keys.libraryDependencies

ThisBuild / scalaVersion := "2.13.4"
Test / parallelExecution := false

lazy val root =
  project.in(file(".")).aggregate(tastyQuery.js, tastyQuery.jvm).settings(publish := {}, publishLocal := {})

lazy val testSources = project.in(file("test-sources")).settings(scalaVersion := "3.0.0-M1")

lazy val tastyQuery =
  crossProject(JSPlatform, JVMPlatform)
    .in(file("."))
    .settings(name := "tasty-query", version := "0.1-SNAPSHOT")
    .settings(scalacOptions += "-Ytasty-reader", scalacOptions += "-Yrangepos")
    .settings(
      libraryDependencies += "org.scala-lang" % "tasty-core_3.0.0-M1" % "3.0.0-M1",
      libraryDependencies += "org.scalameta" %% "munit"               % "0.7.22" % Test,
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
