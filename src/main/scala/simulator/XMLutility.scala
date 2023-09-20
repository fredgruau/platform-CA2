package simulator

import java.awt.Color
import java.io.{BufferedReader, FileReader, IOException}
import scala.::
import scala.collection.JavaConverters._
import scala.collection.immutable
import scala.xml.{Atom, Elem, Node, Text, XML}
/** contains static function to extract information from an UML node */
object XMLutilities {

  def isParenthesis(c: Char): Boolean = c == '(' || c == ')'

  /**
   *
   * @param s encoding of one tree with parenthesis
   * @return an xml hierarchy with branch representing layers, and leaf representing fields,
   */
  def readXmlTree(s: String): Elem = {
    assert(s(0) == '(')
    var iCur: Int = 1 //iCur parcourt all of s

    /** Read one Layer or one field starting at index iCur no parenthesis */
    def readOne(): Elem = {
      //meet next parenthesis so as to retrieve the name
      val i0 = iCur
      while (!isParenthesis(s(iCur))) iCur += 1
      val name = s.substring(i0, iCur)
      assert(name.size > 0)
      s(iCur) match {
        case ')' => // iCur+=1 //consumes ')'
          <field>
            {name}
          </field>
        case '(' => //repeat read one node until matching ')'is found
          val nodes: List[Node] = readMany(); //iCur+=1 //consumes closing parenthesis
          <layer>
            {name}{nodes}
          </layer> //y a pas de node layers.
      }
    }

    /** Read several layer or field, each  between a pair of parenthesis */
    def readMany(): List[Elem] = {
      var res: List[Elem] = List.empty
      while (iCur < s.length && s(iCur) == '(') {
        iCur += 1 //consume the '('
        res ::= readOne() //repeat read one node until matching ')'is found
        iCur += 1 //consume the ')'
      }
      assert(iCur == s.length || s(iCur) == ')') //we  have gone through the list, so it must be closing, or the whole string has been gore
      return res
    }

    readOne() //return the root node
  }

  /**
   *
   * @param path acces vers un fichier
   * @return le xml contenu dans ce fichier
   */
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
   * @param node to be tested
   * @return true if the node is not a branch nor a leaf of the hierarchy of layers
   */
  def isSpurious(node: Node) = node.isInstanceOf[Text] || node.isInstanceOf[Atom[String]]
  /**
   *
   * @param node a root node of xml tree
   * @return the text associated to  the node, that implies looking for the children being either Text or Atoms.
   */
  def extractNodeText(node: Node) = {
    val all = (node :: node.child.toList)
    val filtered = all.filter(isSpurious(_))
    val texts = filtered.map(_.text)
    val res = texts.mkString("").trim
    res
    // (node :: node.child.toList).filter(_.isInstanceOf[Text]).map(_.text).mkString("").trim
  }

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

  def xArrayString(node: scala.xml.Node, tag: String, attrb: String): Array[String] =
    ((node \\ tag) \ attrb).text.trim.split(",")

  def xInt(node: scala.xml.Node, tag: String, attrb: String) =
    x(node, tag, attrb).toInt

  def xBool(node: scala.xml.Node, tag: String, attrb: String) =
    x(node, tag, attrb).toBoolean


  def fromXMLasHashMap(node: scala.xml.Node, tag: String, attrb: String): Map[String, String] = {
    val node2 = (node \\ tag).head
    immutable.HashMap[String, String]() ++
      node2.child.filterNot(_.isInstanceOf[Text]).map(
        (n: Node) => extractNodeText(n) -> (n \ attrb).text.trim)
  }
}