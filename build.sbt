organization := "edu.uta"
version := "0.1-SNAPSHOT"
scalaVersion := "2.12.3"
licenses += "Apache-2.0" -> url("http://opensource.org/licenses/Apache-2.0")
credentials += Credentials(Path.userHome / ".ivy2" / ".sbtcredentials")
sourceDirectory in Compile := baseDirectory.value / "src" / "main"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.6"

lazy val root = (project in file("."))
  .settings(
     name := "Array Comprehensions",
     libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value,
     initialCommands in console := """import edu.uta.array._
          import scala.io.Source
          import scala.collection.parallel.ParIterable
     """
)
