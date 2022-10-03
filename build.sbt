import sbt.Keys.libraryDependencies
import sbt.internal.util.ManagedLogger

import org.scalajs.jsenv.nodejs.NodeJSEnv

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
  crossProject(JSPlatform, JVMPlatform).in(file("tasty-query"))
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

lazy val examples = project
  .in(file("examples"))
  .dependsOn(tastyQuery.jvm)
  .settings(
    commonSettings,
    Compile / publishArtifact := false,
    fork := true,
    envVars ++= (tastyQuery.jvm / Test / envVars).value,
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
