name := "diablo"
organization := "edu.uta"
version := "0.1"
scalaVersion := "2.12.12"
licenses += "Apache-2.0" -> url("http://opensource.org/licenses/Apache-2.0")
libraryDependencies ++= Seq("org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2",
                            "org.scala-lang" % "scala-reflect" % scalaVersion.value,
                            "org.apache.spark" %% "spark-core" % "3.0.0",
                            "org.apache.spark" %% "spark-sql" % "3.0.0",
                            "org.apache.spark" %% "spark-streaming" % "3.0.0",
                           )
artifactName := { (sv: ScalaVersion, m: ModuleID, a: Artifact) => "../../lib/diablo.jar" }
