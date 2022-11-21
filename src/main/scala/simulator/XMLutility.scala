package simulator

import java.awt.Color
import java.io.{BufferedReader, FileReader, IOException}

import scala.collection.JavaConverters._
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
    val children: collection.Seq[Node] = node.child.filterNot(_.isInstanceOf[Text])
    children.map(_.child.text.trim.asInstanceOf[String])
  }


  def fromXMLasList(node: scala.xml.Node, tag: String, tag2: String, attrb: String) = {
    val children: collection.Seq[Node] = (node \\ tag).head \\ tag2
    children.map(_ \ attrb).map(_.text.trim)
  }

  def fromXMLasListInt(node: scala.xml.Node, tag: String, tag2: String, attrb: String) = {
    fromXMLasList(node, tag, tag2, attrb).map(_.toInt)
  }

  def fromXMLasListIntCouple(node: scala.xml.Node, tag: String, tag2: String, attrb: String, attrb2: String) = {
    fromXMLasListInt(node, tag, tag2, attrb) zip fromXMLasListInt(node, tag, tag2, attrb2)
  }


  def x(node: scala.xml.Node, tag: String, attrb: String): String =
    ((node \\ tag) \ attrb).text.trim

  def xInt(node: scala.xml.Node, tag: String, attrb: String) =
    x(node, tag, attrb).toInt


  def fromXMLasHashMap(node: scala.xml.Node, tag: String, attrb: String): Map[String, String] = {
    val node2 = (node \\ tag).head
    immutable.HashMap[String, String]() ++
      node2.child.filterNot(_.isInstanceOf[Text]).map(
        (n: Node) => extractNodeText(n) -> (n \ attrb).text.trim)
  }
}