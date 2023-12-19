import sbt.Keys.libraryDependencies
import sbt.internal.util.ManagedLogger

import org.scalajs.jsenv.nodejs.NodeJSEnv

val usedScalaCompiler = "3.3.1"
val usedTastyRelease = usedScalaCompiler
val scala2Version = "2.13.12"

val SourceDeps = config("sourcedeps").hide

val rtJarOpt = taskKey[Option[String]]("Path to rt.jar if it exists")
val javalibEntry = taskKey[String]("Path to rt.jar or \"jrt:/\"")

inThisBuild(Def.settings(
  crossScalaVersions := Seq(usedScalaCompiler),
  scalaVersion := usedScalaCompiler,

  scalacOptions ++= Seq(
    "-deprecation",
    "-feature",
    "-encoding",
    "utf-8",
  ),

  scmInfo := Some(
    ScmInfo(
      url("https://github.com/scalacenter/tasty-query"),
      "scm:git@github.com:scalacenter/tasty-query.git",
      Some("scm:git:git@github.com:scalacenter/tasty-query.git")
    )
  ),
  organization := "ch.epfl.scala",
  homepage := Some(url(s"https://github.com/scalacenter/tasty-query")),
  licenses += (("Apache-2.0", url("https://www.apache.org/licenses/LICENSE-2.0"))),
  developers := List(
    Developer("sjrd", "Sébastien Doeraene", "sjrdoeraene@gmail.com", url("https://github.com/sjrd/")),
    Developer("bishabosha", "Jamie Thompson", "bishbashboshjt@gmail.com", url("https://github.com/bishabosha")),
  ),
  versionPolicyIntention := Compatibility.BinaryAndSourceCompatible,
  // Ignore dependencies to internal modules whose version is like `1.2.3+4...` (see https://github.com/scalacenter/sbt-version-policy#how-to-integrate-with-sbt-dynver)
  versionPolicyIgnoredInternalDependencyVersions := Some("^\\d+\\.\\d+\\.\\d+\\+\\d+".r)
))

val commonSettings = Seq(
  Test / parallelExecution := false,
  // Skip `versionCheck` for snapshot releases
  versionCheck / skip := isSnapshot.value
)

val strictCompileSettings = Seq(
  scalacOptions ++= Seq(
    "-Xfatal-warnings",
    "-Yexplicit-nulls",
    "-Ysafe-init",
    "-source:future",
  ),
)

lazy val root = project.in(file("."))
  .aggregate(tastyQuery.js, tastyQuery.jvm).settings(
    publish / skip := true,
  )

lazy val scala2TestSources = crossProject(JSPlatform, JVMPlatform)
  .crossType(CrossType.Pure)
  .in(file("scala2-test-sources"))
  .settings(commonSettings)
  .settings(
    scalaVersion := scala2Version,
    publish / skip := true,
    scalacOptions += "-Xfatal-warnings",
    libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value % "provided",
  )

lazy val testSources = crossProject(JSPlatform, JVMPlatform)
  .crossType(CrossType.Pure)
  .in(file("test-sources"))
  .settings(commonSettings)
  .settings(
    publish / skip := true,
    scalacOptions += "-Xfatal-warnings",
    javacOptions += "-parameters",
  )
  .dependsOn(scala2TestSources)

lazy val tastyQuery =
  crossProject(JSPlatform, JVMPlatform).in(file("tasty-query"))
    .dependsOn(testSources % Test)
    .settings(commonSettings)
    .settings(strictCompileSettings)
    .settings(name := "tasty-query")
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
        val testSourcesCP = Attributed.data((testSources.jvm / Compile / fullClasspath).value)
        val testClasspath = (javalib +: testSourcesCP.map(_.getAbsolutePath())).mkString(";")

        val testResourcesCode =
          ((LocalRootProject / baseDirectory).value / "test-sources/src").getAbsolutePath()

        Map(
          "TASTY_TEST_CLASSPATH" -> testClasspath,
          "TASTY_TEST_SOURCES" -> testResourcesCode,
        )
      },

      mimaBinaryIssueFilters ++= {
        import com.typesafe.tools.mima.core.*
        Seq(
          // Everything in tastyquery.reader is private[tastyquery] at most
          ProblemFilters.exclude[Problem]("tastyquery.reader.*"),
        )
      },

      tastyMiMaPreviousArtifacts := mimaPreviousArtifacts.value,
      tastyMiMaConfig ~= { prev =>
        import tastymima.intf._
        prev
          .withMoreArtifactPrivatePackages(java.util.Arrays.asList(
            "tastyquery",
          ))
      },
    )
    .jvmSettings(
      fork := true,
      Test / javalibEntry := (Test / rtJarOpt).value.getOrElse("jrt:/modules/java.base/"),
    )
    .jsSettings(
      Test / javalibEntry := {
        val rtJar = (Test / rtJarOpt).value

        val s = streams.value
        val targetRTJar = target.value / "extracted-rt.jar"

        rtJar.getOrElse {
          if (!targetRTJar.exists()) {
            s.log.info(s"Extracting jrt:/modules/java.base/ to $targetRTJar")
            extractRTJar(targetRTJar)
          }
          targetRTJar.getAbsolutePath()
        }
      },

      scalaJSUseMainModuleInitializer := true,
      scalaJSLinkerConfig ~= (_.withModuleKind(ModuleKind.CommonJSModule)),
      jsEnv := new NodeJSEnv(NodeJSEnv.Config().withArgs(List("--enable-source-maps"))),
    )

def extractRTJar(targetRTJar: File): Unit = {
  import java.io.{IOException, FileOutputStream}
  import java.nio.file.{Files, FileSystems}
  import java.util.zip.{ZipEntry, ZipOutputStream}

  import scala.jdk.CollectionConverters._
  import scala.util.control.NonFatal

  val fs = FileSystems.getFileSystem(java.net.URI.create("jrt:/"))

  val zipStream = new ZipOutputStream(new FileOutputStream(targetRTJar))
  try {
    val javaBasePath = fs.getPath("modules", "java.base")
    Files.walk(javaBasePath).forEach({ p =>
      if (Files.isRegularFile(p)) {
        try {
          val data = Files.readAllBytes(p)
          val outPath = javaBasePath.relativize(p).iterator().asScala.mkString("/")
          val ze = new ZipEntry(outPath)
          zipStream.putNextEntry(ze)
          zipStream.write(data)
        } catch {
          case NonFatal(t) =>
            throw new IOException(s"Exception while extracting $p", t)
        }
      }
    })
  } finally {
    zipStream.close()
  }
}
