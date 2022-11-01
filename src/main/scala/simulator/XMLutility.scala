package simulator

import java.awt.Color
import java.io.{BufferedReader, FileReader, IOException}

import scala.collection.immutable
import scala.xml.{Node, Text, XML}

object XMLutilities {

  def readXML(path: String): Node = {
    val lecteur = new BufferedReader(new FileReader(path))
    try {
      XML load lecteur
    }
    catch {
      case _: IOException => <error>Error reading XML file.</error>
    }
  }

  /**
   *
   * @param node a root node of xml tree
   * @return the text of the node
   */
  def extractNodeText(node: Node) = (node :: node.child.toList).filter(_.isInstanceOf[Text]).map(_.text).mkString("").trim

  /**
   * @param node containing a list of elements with identical IDs,
   * @return the list of text associated to those elements.
   */
  def fromXMLasList(node: scala.xml.Node) = {
    val children = node.child.filterNot(_.isInstanceOf[Text])
    children.map(_.child.text.trim.asInstanceOf[String])
  }

  def fromXMLasHashMap(node: scala.xml.Node) = immutable.HashMap[String, Color]() ++
    (node.child.filterNot(_.isInstanceOf[Text]).map((n: Node) => (extractNodeText(n) -> {
      new Color(Integer.decode((n \ "@color").text.trim))
    })))
}