import sbt.Keys.libraryDependencies

ThisBuild / scalaVersion := "2.13.4"

lazy val root = project.in(file(".")).
                       aggregate(tastyQuery.js, tastyQuery.jvm).
                       settings(
                         publish := {},
                         publishLocal := {},
                       )

lazy val tastyQuery =
  crossProject(JSPlatform, JVMPlatform)
    .in(file("."))
    .settings(
      name := "tasty-query",
      version := "0.1-SNAPSHOT",
    )
    .settings(scalacOptions += "-Ytasty-reader")
    .settings(
      libraryDependencies += "org.scala-lang" % "tasty-core_3.0.0-M1" % "3.0.0-M1"
    )
    .jvmSettings(
    )
    .jsSettings(
      scalaJSUseMainModuleInitializer := true,
    )
