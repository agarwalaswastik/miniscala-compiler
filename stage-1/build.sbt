scalaVersion := "2.12.18"

scalacOptions in ThisBuild ++= Seq("-unchecked", "-deprecation", "-feature")

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.9" % "test"

excludeFilter in unmanagedSources := HiddenFileFilter || "*sample*"

logBuffered in Test := false

parallelExecution in Test := false

