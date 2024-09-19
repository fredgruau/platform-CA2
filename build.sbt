name := "platform-CA2"

version := "0.1"
//scalaVersion := "2.13.12"
scalaVersion := "2.13.1"   //ce que j'avais originellement avant tortue sandwich

//scalaVersion := "2.13.10"
githubTokenSource := TokenSource.GitConfig("github.token")
resolvers += Resolver.githubPackages("TortueSandwich")

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.8" % "test"

libraryDependencies += "org.scala-lang.modules" %% "scala-swing" % "3.0.0"

//libraryDependencies += "com.github.benhutchison" % "scalaswingcontrib" % "1.8"

libraryDependencies += "org.scala-lang.modules" %% "scala-xml" % "1.3.0"


//libraryDependencies += "org.scalafx" %% "scalafx" % "21.0.0-R32"

libraryDependencies += "blob" % "quadedgetriangulation_2.13" % "1.+"

//libraryDependencies +=  "quadedgetriangulation_2.13" % "1.2"

