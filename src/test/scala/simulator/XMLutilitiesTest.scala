package simulator

import org.scalatest.{BeforeAndAfter, FunSuite}
import simulator.XMLutilities.{extractNodeText, readXmlTree}

class XMLutilitiesTest extends FunSuite {
  val displayableLayer: String = "layer" + "(seed(llseed))" + "(def(F)(E)(Ve))"

  /** we were filtering only Text class, it turned out that we should also select Atom, because they are used when the xml is built using litteral */
  test("readXmlTree") {
    val input = 141 //not to big int
    val xmlDisplayableLayer = // <layer>layer<layer>def<field>Ve</field><field>E</field><field>F</field></layer><layer>seed<field>llseed</field></layer></layer>
      readXmlTree(displayableLayer)
    System.out.println(xmlDisplayableLayer)
    assert(extractNodeText(xmlDisplayableLayer).size > 0)
  }
  test("elementary") {
    val name: String = "toto"
    val x = <layer>
      {name}
    </layer> //name is placed in an atom
    System.out.println(x.child.size)
    assert(extractNodeText(x).size > 0)
  }
}
