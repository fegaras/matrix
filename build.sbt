organization := "edu.uta"
version := "0.1-SNAPSHOT"
scalaVersion := "2.11.7"
licenses += "Apache-2.0" -> url("http://opensource.org/licenses/Apache-2.0")
credentials += Credentials(Path.userHome / ".ivy2" / ".sbtcredentials")
sourceDirectory in Compile := baseDirectory.value / "src" / "main"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.6"

lazy val `matrix-spark` = (project in file("."))
  .settings(
     unmanagedSourceDirectories in Compile += baseDirectory.value / "src" / "spark",
     libraryDependencies += "org.apache.spark" %% "spark-core" % "2.2.0",
     initialCommands in console := """import edu.uta.matrix._
          import org.apache.spark._
          import org.apache.spark.rdd._
          val sc = new SparkContext(new SparkConf().setAppName("Test").setMaster("local[2]"))
     """,
     cleanupCommands in console := "sc.stop()"
  )

lazy val root = `matrix-spark`
