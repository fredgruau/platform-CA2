package simulator

import java.awt.Color

import scalaswingcontrib.tree.{ExternalTreeModel, InternalTreeModel, Tree, TreeModel}

import scala.swing.{Action, BorderPanel, Button, Component, Dimension, GridPanel, Label, MainFrame, ScrollPane, SimpleSwingApplication, Swing, TabbedPane}
import compiler.V
//import javax.swing.Renderer
import javax.swing.event.{TreeExpansionEvent, TreeExpansionListener}
import scalaswingcontrib.tree.Tree.Path
import scalaswingcontrib.tree.{Tree, TreeModel}
import simulator.XMLutilities.extractNodeText
import Tree.{Renderer}

import scala.swing.event.MouseClicked
import scala.xml.{Node, Text}


import scala.swing._
import Swing._
import scala.collection.immutable.HashMap
import scala.swing.{Dimension}
import scala.xml.XML

/**
 * Allows to browse the layer
 *
 * @param xmlLayerTree fixed file, containing the layer structure
 * @param controller
 */
class LayerTree(val xmlLayerTree: Node, val controller: Controller) extends Tree[Node] with TreeExpansionListener {
  //  former version model = TreeModel(xmlDoc)(_.child filterNot (_.text.trim.isEmpty))
  // preferredSize = (width,height): Dimension
  //background = Color.lightGray

  import Simulator.ExampleData._

  model = TreeModel(xmlLayerTree)(_.child filterNot (_.isInstanceOf[Text]))
  renderer = Renderer.labeled[Node] { n =>
    val icon =
      if (controller.colorDisplayedField.contains(extractNodeText(n)))
        new DiamondIcon(V(), controller.colorDisplayedField(extractNodeText(n)), true)
      else if (isLayer((n))) folderIcon
      else fileIcon
    (icon, extractNodeText(n))
  }
  // if (n.label startsWith "#") n.text.trim   else /*n.label + ":" +*/


  //we use javax swing for listening to expansion event, because we failed to use scala swing
  peer.addTreeExpansionListener(this)

  listenTo(mouse.clicks)
  reactions += {
    case MouseClicked(_, pp, _, _, _) =>
      val p = peer.getPathForLocation(pp.x, pp.y) //Jtree utility that allows to retrieve the node clicked
      if (p != null && p.last.label == "field") { //only field"s node can have a color
        val s = extractNodeText(p.last)
        println("mouseClick  " + s)
        publish(new ToggleColorEvent(s)) //forward the event to the controller in a clean way.
      }
  }
  expandExpandedDescendant(xmlLayerTree, Vector(xmlLayerTree)) //Vector(xmlDoc) is the pasth to xmlDoc

  private def isLayer(n: Node): Boolean = n.label == "layer"

  // Required by TreeExpansionListener interface.
  override def treeExpanded(e: TreeExpansionEvent): Unit = publish(ExpandLayer(extractNodeText(e.getPath.last))) //Forwards a clean ScalaSwing event

  override def treeCollapsed(e: TreeExpansionEvent): Unit = publish(CollapseLayer(extractNodeText(e.getPath.last))) //Forwards a clean ScalaSwing event
  /**
   *
   * @param t current node of XML tree representing layers
   * @param p path to that node
   *          check if the layers encoded by t where already expanded in a previour run, and if so, expands them directly
   */
  def expandExpandedDescendant(t: Node, p: Path[Node]): Unit = {
    val layerName = extractNodeText(t)
    if (controller.expandedLayers.contains(layerName)) {
      expandPath(p)
      for (c <- t.child) //ici on peut mettre un if et tester si la couche doit etre expanded ou non
        expandExpandedDescendant(c, p :+ c)
    }
  }


}
