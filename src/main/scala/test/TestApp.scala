package test

import scala.swing._

object TestApp extends SimpleSwingApplication {
  def top = new MainFrame {
    title = "Hello"
    contents = new Label("Hello World")
  }
}