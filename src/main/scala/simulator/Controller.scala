package simulator

import java.awt.Color

import simulator.XMLutilities.{fromXMLasHashMap, fromXMLasList, readXML}

import scala.swing._
import Swing._
import scala.collection.immutable.HashMap
import scala.swing.{Component, Dimension}
import scala.xml.XML
import colors.mainColors
import compiler.Locus

class Controller(val nameCA: String, locusDisplayed: Map[String, Locus]) extends Component() {
  var layerTree: LayerTree = null //cannot be passed upon creation of controller,
  // because of mutual recursive link between controller and layerTree
  def init(lt: LayerTree) = {
    listenTo(lt)
    layerTree = lt //we will need to repaint it upond expansion or coloring
  }

  //State variables, read and stored in a xmlTree
  var XMLparamCA = readXML("src/main/scala/compiledCA/" + nameCA + "param.xml")
  /** Colors of displayed layers */
  var colorOfFields: HashMap[String, Color] = fromXMLasHashMap((XMLparamCA \\ "colorOfField").head)
  /** contains all the layers which are expanded */
  var expandedLayers: Set[String] = fromXMLasList((XMLparamCA \\ "expandedLayer").head).toSet

  override def toString = "expanded Layers: " + expandedLayers + "\n" + colorOfFields + "\n"


  /** updates the xml containing all the Param of the CAs */
  private def updateAndSaveXMLparamCA() = {
    XMLparamCA =
      <paramCA>
        <expandedLayer>
          {expandedLayers.map(nameLayer => <Layer>
          {nameLayer}
        </Layer>)}
        </expandedLayer>
        <colorOfField>
          {colorOfFields.keys.map(nameField => {
          val c = colorOfFields(nameField) //we and with 0xFFFFFF because we do use the alpha parameter
          <layer color={"0x" + (c.getRGB).toHexString.toUpperCase.drop(2)}>
            {nameField}
          </layer>
        })}
        </colorOfField>
      </paramCA>
    XML.save("src/main/scala/compiledCA/" + nameCA + "param.xml", XMLparamCA)
  }

  /** process the signal */

  maximumSize = (0, 0): Dimension //there is nothing to show, we therefore give it O dimension!
  //   listenTo(layerTree) //it process expansion, collapse, and toggleColor events

  reactions += {
    case ExpandLayer(s) =>
      expandedLayers += s;
      updateAndSaveXMLparamCA()
      layerTree.repaint()
    case CollapseLayer(s) =>
      expandedLayers -= s;
      updateAndSaveXMLparamCA()
      layerTree.repaint()
    case ToggleColorEvent(s) =>
      colorOfFields =
        if (colorOfFields.contains(s))
          colorOfFields - s
        else {
          val mainColorLeft = mainColors.toSet.diff(colorOfFields.values.toSet)
          if (mainColorLeft.nonEmpty) {
            var naturalChoice = Math.abs(s.hashCode) % mainColors.size
            while (!mainColorLeft.contains(mainColors(naturalChoice)))
              naturalChoice = (naturalChoice + 1) % mainColors.size //look for the first main color not used yet
            colorOfFields + (s -> mainColors(naturalChoice))
          }
          else colorOfFields //we could not find a new color, nothing will change
        }
      updateAndSaveXMLparamCA()
      layerTree.repaint()
  }
}

import java.awt.Color._
import Integer.decode

object colors {
  //primary, secondary and tertiary colors aranged on a "color wheel" which exhibits a toroidal metric.
  val chartreuseGreen = new Color(decode("0x80FF00"))
  val springGreen = new Color(decode("0x00FF80"))
  val azure = new Color(decode("0x0080FF"))
  val violet = new Color(decode("0x8000FF"))
  val rose = new Color(decode("0xFF0080"))
  val mainColors = Array(red, orange, yellow, chartreuseGreen, green, springGreen, cyan, azure, blue, violet, magenta, rose)
  //gray tones are used for fixed system layers such as debug, liveIf,
  val grays = Array(darkGray, gray, lightGray, white)
}
