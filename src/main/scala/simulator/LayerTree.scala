package simulator

import compiler.{ProduceJava, V}
import dataStruc.Named
import dataStruc.Util.lastPathPart
import scalaswingcontrib.tree.{Tree, TreeModel}
import scalaswingcontrib.tree.Tree.{Path, Renderer}
import simulator.ExampleData._
import simulator.XMLutilities.{extractNodeText, isSpurious}

import javax.swing.JTree
import javax.swing.event.{TreeExpansionEvent, TreeExpansionListener}
import scala.swing.event.MouseClicked
import scala.xml.{Atom, Node, Text}

/**
 * Tree swing component, allowing  to easily browse the layer and select layers for display
 *
 * @param xmlLayerTree fixed file, containing the layer structure
 * @param controller   the controller
 */
class LayerTree(val xmlLayerTree: Node, val controller: Controller) extends Tree[Node] with TreeExpansionListener {
  def hideRoot = {
    peer.setRootVisible(false) //marche pas
    peer.setShowsRootHandles(true) //marche pas
  }

  hideRoot

  peer.addTreeExpansionListener(this) //we had to resort to directly use javax swing for listening to expansion event, because we failed to use scala swing
  model = TreeModel(xmlLayerTree)(_.child filterNot (isSpurious(_))) //text are also nodes, we do not want those
  hideRoot

  /** returns "prev" if the field is the layer previous value, otherwise, the last part of the path* */
  def reducedText(s: String) =
    if (Named.isLayer(s)) "prev"
    else lastPathPart(s)
  renderer = Renderer.labeled[Node] { n => //
    val icon =
      if (controller.colorDisplayedField.contains(extractNodeText(n))) //test if the field is to be displayed
        new DiamondIcon(V(), controller.colorDisplayedField(extractNodeText(n)), true) //if so displays its color, diamond should be different depending on  locus
      else if (isLayer(n)) folderIcon //layers contains other layers, therefore they display as folder
      else fileIcon //those are not yet displayed field
    (icon, reducedText(extractNodeText(n))) //we also display layers or field's name
  }
  hideRoot
  listenTo(mouse.clicks)
  hideRoot
  reactions += {
    case MouseClicked(_, pp, _, _, _) =>
      val p = peer.getPathForLocation(pp.x, pp.y) //we resorted to that Jtree utility that allows to retrieve the node clicked
      if (p != null && (p.last.label == "field" || (p.last.label == "layer"))) { //only field"s node can have a color
        val s = extractNodeText(p.last)
        // println("mouseClick  " + s)
        publish(ToggleColorEvent(s)) //forward the event to the controller in a clean way, so that it can update what is dipalayed.
      }
  }
  expandExpandedDescendant(xmlLayerTree, Vector(xmlLayerTree)) //exands already expanded node. Vector(n) is the path to n.
  hideRoot

  private def isLayer(n: Node): Boolean = n.label == "layer" //being a layer or not is determined by the label in the xml file

  // Required by TreeExpansionListener interface.
  override def treeExpanded(e: TreeExpansionEvent): Unit = publish(ExpandLayer(extractNodeText(e.getPath.last))) //Forwards a clean ScalaSwing event

  override def treeCollapsed(e: TreeExpansionEvent): Unit = publish(CollapseLayer(extractNodeText(e.getPath.last))) //Forwards a clean ScalaSwing event
  /**
   *
   * @param t current node of XML tree representing layers
   * @param p path to that node
   *          check if the layers encoded by t where already expanded in a previour run, and if so, expands them directly
   */
  private def expandExpandedDescendant(t: Node, p: Path[Node]): Unit = {
    val layerName = extractNodeText(t)
    if (controller.expandedLayers.contains(layerName)) {
      expandPath(p)
      for (c <- t.child) //ici on peut mettre un if et tester si la couche doit etre expanded ou non
        expandExpandedDescendant(c, p :+ c)
    }

  }

}
