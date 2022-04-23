name := "diablo"
organization := "edu.uta"
version := "0.2"
scalaVersion := "2.12.15"
val sparkVersion = "3.2.1"
licenses += "Apache-2.0" -> url("http://opensource.org/licenses/Apache-2.0")

libraryDependencies ++= Seq("org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2",
                            "org.scala-lang" % "scala-reflect" % scalaVersion.value,
                            "org.apache.spark" %% "spark-core" % sparkVersion,
                            "org.apache.spark" %% "spark-sql" % sparkVersion,
                            "org.apache.spark" %% "spark-streaming" % sparkVersion
                           )

libraryDependencies ++= {
  CrossVersion.partialVersion(scalaVersion.value) match {
    case Some((2, major)) if major <= 12 =>
      Seq()
    case _ =>
      Seq("org.scala-lang.modules" %% "scala-parallel-collections" % "1.0.4")
  }
}

// Use BLAS:
// libraryDependencies += "com.github.fommil.netlib" % "all" % "1.1.2" pomOnly()

scalacOptions ++= Seq(//"-deprecation",
                      "-Xno-patmat-analysis")

artifactName := { (sv: ScalaVersion, m: ModuleID, a: Artifact) => "../../lib/diablo.jar" }
