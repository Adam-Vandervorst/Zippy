ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.4.1"
// https://github.com/scala/scala3/issues/20266
ThisBuild / scalacOptions += "-source:3.3"

lazy val root = (project in file("."))
  .settings(
    name := "Zippy"
  )
