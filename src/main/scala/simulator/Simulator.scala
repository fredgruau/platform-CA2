package simulator

import javax.swing.event.TreeExpansionEvent
import java.awt.{Color, Polygon}

import javax.swing._
import javax.swing.tree._
import javax.swing.event._

import scala.collection.immutable.HashMap
import scalaswingcontrib.tree.Tree.Path

import scala.swing.{Component, SimpleSwingApplication}
import scala.swing.TabbedPane.Page
import scala.swing.event.MouseClicked
import scala.xml._
import scalaswingcontrib.tree.{ExternalTreeModel, InternalTreeModel, Tree, TreeModel}
import scalaswingcontrib.event.TreeNodeSelected

import scala.collection.{immutable, mutable}
import Tree.{Editor, Renderer}
import compiler.{Locus, Ring, V}
import DynamicClassUtility._
import javax.swing.text.Element

import scala.swing.{Action, BorderPanel, Button, Component, Dimension, GridPanel, Label, MainFrame, ScrollPane, SimpleSwingApplication, Swing, TabbedPane}
import Swing.{Icon, pair2Dimension}
import scala.swing.event.Event
import scala.collection.JavaConverters._
//import scala.jdk.CollectionConverters
import java.io._

import java.awt.Color
import XMLutilities._


object Simulator extends SimpleSwingApplication {
  var nameCA: String = " "

  override def startup(args: Array[String]): Unit = {
    nameCA = args(0) //this is done before top is launched,
    //we create the different swing components in top, so that
    //we can access the nameCA of the CA in order to open the appropriate files.
    super.startup(args)
  }

  override def main(args: Array[String]) = {
    super.main(args)
  }

  // preferredSize = new Dimension(320, 320)

  def top = new MainFrame {
    title = "cellular automata"
    val classCA = loadClass("compiledCA." + nameCA)
    val progCA: CAloops = getProg(classCA)
    val locusDisplayed: Map[String, Locus] = progCA.printedLayerLocus.asScala.toMap
    //tobemoved to CApanel
    val offsetDisplayed: Map[String, List[Integer]] = progCA.printedLayerOfset.asScala.toMap

    val bitSizeDisplayed: Map[String, Integer] = progCA.printedLayerBitSize().asScala.toMap

    /** process the signal we create controller first in order to instanciate state variable used by tree */
    val controller = new Controller(nameCA, locusDisplayed)
    val xmlLayerTree = readXML("src/main/scala/compiledCA/" + nameCA + "layer.xml")
    /** Tree for browsing the hierarchy of layers and which field to display */
    val layerTree = new LayerTree(xmlLayerTree, controller)
    val scrollableXmlTree = new ScrollPane(layerTree) //we put it scrollable because it can become big
    controller.init(layerTree)
    val env = new Env(progCA, 0)
    val caPanel = new CApannel(env)
    contents = new BorderPanel {

      import BorderPanel.Position._

      layout(scrollableXmlTree) = West
      layout(controller) = East
      layout(caPanel) = Center
    }
    size = (1024, 768): Dimension
    //contents=new ScrollPane(xmlTree)
    // contents= new SplitPane(Orientation.Vertical, new ScrollPane(xmlTree){preferredSize = (1024, 768): Dimension}, new Controller(xmlTree)) {  continuousLayout = true  }
    //This setting allows go insert the contoler as a pannel, without wasting space
    //contents=new FlowPanel{ contents+=new ScrollPane(xmlTree);contents+=controller}
  }

  object ExampleData {
    // File system icons
    def getIconUrl(path: String) = resourceFromClassloader(path) ensuring(_ != null, "Couldn't find icon " + path)

    // val fileIcon = Icon(getIconUrl("/scalaswingcontrib/test/images/file.png"))
    //   val folderIcon = Icon(getIconUrl("/scalaswingcontrib/test/images/folder.png"))
    val fileIcon = Icon("src/ressources/file.png")
    val folderIcon = Icon("src/ressources/folder.png")
  }

  /** contains the types used in the simulator */
  object CAtype {
    /** for each layer that needs to be initialized, we
     * supply a function whose first two argument are the width and height of the CA,
     * while the third is the adress in memory, and will range in 0..(witdth*height)/32
     * the function InitLayer(width,height,adr) will return the integer to be stored
     * in Mem[witdth*height)/32], or the array of integer,to be stored if there needs to be several
     * either because it is not boolean or because it is not vertice.
     * */
    type InitLayers = Map[String, Function3[Int, Int, Int, Seq[Int]]]
    /** stores all the memory fields of a CA */
    type CAmem = Array[Array[Int]]

    /** allows to reuse the same code for displaying or for generating svg */
    trait myGraphics2D {
      def setColor(c: Color): Unit

      def fillPolygon(p: Polygon): Unit

      def drawPolygon(p: Polygon): Unit

    }

  }

}
