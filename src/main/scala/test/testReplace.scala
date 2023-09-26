package test

object testReplace extends App {
  val src = "bon#ee#eeee"
  val res = src.replace('#', '$')
  System.out.print(res)
}
