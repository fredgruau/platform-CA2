package simulator

import java.awt.Color

import simulator.XMLutilities._

import scala.swing._
import Swing._
import scala.collection.immutable.HashMap
import scala.swing.{Component, Dimension}
import scala.xml.{Node, NodeSeq, XML}
import colors.mainColors
import compiler.Locus
import simulator.Simulator.CAtype.CAMem

import scala.collection.JavaConverters._
import scala.collection.MapView

/**
 *
 * @param param mutable  because updated as we interact with display, and also stored
 * @param progCA
 */
class Controller(val nameCA: String, var param: Node, val progCA: CAloops) extends Component() {
  val locusDisplayedField: Map[String, Locus] = progCA.fieldLocus.asScala.toMap
  val bitSizeDisplayedField: Map[String, Int] = progCA.fieldBitSize().asScala.mapValues(_.toInt).toMap
  val initName: Map[String, String] = fromXMLasHashMap(param, "inits", "@init")


  /** memory offset of the bit planes  represening  field */
  private val memFieldsOffset: Map[String, List[Integer]] = progCA.fieldOffset().asScala.toMap

  /**
   *
   * @param fieldName name of a field that we want to read
   * @param CAmem     CA memory
   * @return array of Int32  storing the  field components
   */
  def memFields(fieldName: String, CAmem: CAMem) =
    memFieldsOffset(fieldName).map(CAmem(_))

  var layerTree: LayerTree = null //cannot be passed upon creation of controller,
  var envList: Vector[Env] = Vector()

  /** layerTree is suplied latter, because of mutual recursive link between controller and layerTree */
  def init(lt: LayerTree) = {
    listenTo(lt)
    layerTree = lt //we will need to repaint it upond expansion or coloring
  }

  /** part of the xml param which cannot be (yet) changed during a simulation */
  val fixed: NodeSeq = param \\ "fixed"
  /** Colors of displayed layers */
  val colorCode: Map[String, String] = fromXMLasHashMap(param, "colorOfField", "@color")
  /** associated a color to each displayed field , fiedls to be displayed are the keys of this map */
  var colorDisplayedField: Map[String, Color] = colorCode.mapValues((s: String) => new Color(Integer.decode(s))).toMap


  /** contains all the layers which are expanded */
  var expandedLayers: Set[String] = fromXMLasList((param \\ "expandedLayer").head).toSet


  override def toString = "expanded Layers: " + expandedLayers + "\n" + colorDisplayedField + "\n"


  /** updates the xml containing all the Param of the CAs
   * we drop the two hexa digit of the alpha component, it is not used */
  private def updateAndSaveXMLparamCA() = {
    param =
      <paramCA>
        {fixed}<expandedLayer>
        {expandedLayers.map(nameLayer => <Layer>
          {nameLayer}
        </Layer>)}
      </expandedLayer>
        <colorOfField>
          {colorDisplayedField.keys.map(nameField => {
          val c = colorDisplayedField(nameField) //we and with 0xFFFFFF because we do use the alpha parameter
          <layer color={"0x" + (c.getRGB).toHexString.toUpperCase.drop(2)}>
            {nameField}
          </layer>
        })}
        </colorOfField>
      </paramCA>
    XML.save("src/main/scala/compiledCA/" + nameCA + "param.xml", param)
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
      colorDisplayedField =
        if (colorDisplayedField.contains(s))
          colorDisplayedField - s
        else { //we add a color
          val mainColorLeft = mainColors.toSet.diff(colorDisplayedField.values.toSet)
          if (mainColorLeft.nonEmpty) {
            var naturalChoice = Math.abs(s.hashCode) % mainColors.size
            while (!mainColorLeft.contains(mainColors(naturalChoice)))
              naturalChoice = (naturalChoice + 1) % mainColors.size //look for the first main color not used yet
            colorDisplayedField + (s -> mainColors(naturalChoice))
          }
          else colorDisplayedField //we could not find a new color, nothing will change
        }
      updateAndSaveXMLparamCA()
      layerTree.repaint()
      for (env <- envList)
        env.repaint()
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
