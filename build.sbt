ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.4.2"
// https://github.com/scala/scala3/issues/20266
ThisBuild / scalacOptions += "-source:3.3"

lazy val root = (project in file("."))
  .settings(
    name := "Zippy",
    libraryDependencies += "org.scalameta" %% "munit" % "1.0.0" % Test,
    libraryDependencies += "org.apache.jena" % "apache-jena-libs" % "5.0.0" pomOnly()
  )
