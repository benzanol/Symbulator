import Dependencies._

enablePlugins(ScalaJSPlugin)

name := "Scala.js Tutorial"
scalaVersion := "2.13.1" // or any other Scala version >= 2.11.12

libraryDependencies += "org.scala-js" %%% "scalajs-dom" % "2.1.0"

// This is an application with a main method
scalaJSUseMainModuleInitializer := true

logLevel := Level.Error

/*
lazy val hello = taskKey[Unit]("Prints 'Hello World'")
hello := {
  import scala.sys.process._
  val cmd = "/home/quaviq/.bin/refresh-firefox" // Your command
  val output = cmd.!! // Captures the output
}

hello := hello.dependsOn(Compile / fastLinkJS).value
 */
