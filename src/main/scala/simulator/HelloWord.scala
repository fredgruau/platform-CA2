package simulator

import scalaswingcontrib.tree.{Tree, TreeModel}
import java.io._
import swing._
import event._

object HelloWorld extends SimpleSwingApplication {
  lazy val infiniteTree = new Tree(TreeModel(1000) { n => 1 to n filter (n % _ == 0) }) {
    expandRow(0)
  }

  def top = new MainFrame {
    title = "Hello, World!"
    contents = infiniteTree
    // new Tree[File] {model = TreeModel(new File(".")) { f =>  if (f.isDirectory) f.listFiles.toSeq else Seq()}}
    //   new Button {  text = "Click Me!"}

  }

  /*
  val menuItems = Node("Hobbies", Node("Skateboarding"),Node("Skateboarding2"))

    val mytree=new Tree[Node[String]] {
      model = TreeModel(menuItems)(_.children)
      renderer = Tree.Renderer(_.value)
    }

}

case class Node[A](value: A, children: Node[A]*)
*/
}