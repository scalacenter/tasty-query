import sbt.Keys.libraryDependencies

val usedScalaCompiler = "3.1.0"
val usedScala2StdLib = "2.13.7"
val usedTastyRelease = usedScalaCompiler

val StdLibClasspath = Configuration.of("StdLibClasspath", "StdLibClasspath")

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
    .configs(StdLibClasspath)
    .settings(
      inConfig(StdLibClasspath)(Defaults.configSettings),
      libraryDependencies ++= Seq(
        "org.scala-lang" % "scala-library" % usedScala2StdLib % StdLibClasspath,
        "org.scala-lang" %% "scala3-library" % usedScalaCompiler % StdLibClasspath,
      ),
    )
    .settings(javaOptions ++= {
      val testResources = {
        val testSourcesProducts = (testSources / Compile / products).value
        // Only one output location expected
        assert(testSourcesProducts.size == 1)
        testSourcesProducts.map(_.getAbsolutePath).head
      }
      val stdLibrary = {
        val parts = (StdLibClasspath / managedClasspath).value.seq.map(_.data)
        parts.mkString(java.io.File.pathSeparator)
      }
      val testResourcesCode = {
        (testSources / sourceDirectory).value.getAbsolutePath
      }
      Seq(
        s"-Dtest-resources=$testResources",
        s"-Dstd-library=$stdLibrary",
        s"-Dtest-resources-code=$testResourcesCode"
      )
    })
    .jvmSettings(
      fork := true,
      libraryDependencies += "commons-io" % "commons-io" % "2.11.0",
    )
    .jsSettings(
      scalaJSUseMainModuleInitializer := true,
      scalaJSLinkerConfig ~= (_.withModuleKind(ModuleKind.ESModule))
    )
