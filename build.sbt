ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.8.1"
// https://github.com/scala/scala3/issues/20266
ThisBuild / scalacOptions += "-source:3.3"
ThisBuild / scalacOptions += "-feature"
ThisBuild / scalacOptions += "-explain"

lazy val root = (project in file("."))
  .settings(
    name := "Zippy",
    libraryDependencies += "org.scalameta" %% "munit" % "1.2.1" % Test,
    libraryDependencies += "org.scala-lang.modules" %% "scala-collection-contrib" % "0.3.0",
  )
