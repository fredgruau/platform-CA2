package simulator

import compiler.{Locus, V}
import simulator.Controller.disableBinding
import simulator.CAtype._
import simulator.ExampleData._
import simulator.Simulator.{displayParam, simulParam}
import simulator.XMLutilities._
import simulator.colors.mainColors

import java.awt.Color
import java.io.FileNotFoundException
import java.util
import javax.swing.{InputMap, JComponent, KeyStroke}
import scala.collection.JavaConverters._
import scala.swing._
import scala.swing.event.{ButtonClicked, Key, KeyReleased, SelectionChanged}
import scala.xml.{Node, NodeSeq, XML}

/**
 *
 * @param nameCA    name used to find out where param and progCA are
 * @param paramCA   mutable  because updated as we interact with display, and also stored
 * @param progCA    contains the code for the loops
 * @param chosenDir directory containing the CA code
 */
class Controller(val nameCA: String, val globalInit: Array[String], var simulParam: Node, var displayParam: Node,
                 val progCA: CAloops2, val chosenDir: String, val mf: MainFrame)
  extends ToolBar() { //the controller inherits the toolBar, so that it can easily identifies which button was ckicqued, using the button's variable  name
  /** we need to know the locus of fields which are either displayed or initialized */
  val locusDisplayedOrDirectInitField: Map[String, Locus] = progCA.fieldLocus.asScala.toMap
  /** we need to know the number of ints of fields which are either displayed or initialized */
  val bitSizeDisplayedOrDirectInitField: Map[String, Int] = progCA.fieldBitSize().asScala.mapValues(_.toInt).toMap
  /** the method used to initialize the direct init fields. */
  // val initName: Map[String, String] = fromXMLasHashMap(simulParam, "inits", "@init")
  val initName: util.HashMap[String, String] = progCA.init() //fromXMLasHashMap(displayParam, "inits", "@init")
  /** memory offset of the bit planes  representing  field, the size of the list corresponds to the density of the field */
  val memFieldsOffset: Map[String, List[Integer]] = progCA.fieldOffset().asScala.toMap
  /** this is for the display, this is not the number of lines and columns. */
  val CAwidth: Int = xInt(simulParam, "display", "@CAwidth")

  /** by default, if not supplied, number of lignes is 1/sqrt(2) number of columns */
  def CAheight: Int = {
    try {
      xInt(simulParam, "display", "@CAheight")
    }
    catch {
      case _: java.lang.NumberFormatException => (CAwidth / Math.sqrt(2)).toInt
    }
  }

  /** Jcomponent displaying the tree of layers which can expands by cliking on it */
  var layerTree: LayerTree = null //cannot be  directly set  upon creation of controller, because of double recursive definition
  /** a controller manages several environements */
  var envList: Vector[Env] = Vector() //cannot be  directly set  upon creation of controller,

  /** layerTree is suplied latter, because of mutual recursive link between controller and layerTree */
  def init(lt: LayerTree): Unit = {
    listenTo(lt) //we will need to repaint it upond expansion or coloring
    layerTree = lt
    layerTree.hideRoot
  }

  /** part of the xml param which cannot be (yet) changed during a simulation */
  private val fixed: NodeSeq = simulParam \\ "fixed"
  /** Colors of displayed layers */
  private val colorCode: Map[String, String] = fromXMLasHashMap(displayParam, "colorOfField", "@color")
  /** associate a color to each displayed field , fiedls names are the keys, colors are the values which need ot be decoded from hexadecimal */
  var colorDisplayedField: Map[String, Color] = colorCode.mapValues((s: String) => new Color(Integer.decode(s))).toMap
  /** We 'll have to generate the voronoi in space. We consider that V() is allways displayed */
  var displayedLocus: Set[Locus] =
    colorDisplayedField.keys.map(locusDisplayedOrDirectInitField(_)).toSet + V()
  /** we'll applies t0 iterations upon initialization to speed up going directly to the interesting cases */
  val t0: Int = xInt(simulParam, "simul", "@t0")
  /** true if we start to play immediately */
  var isPlaying: Boolean = xBool(simulParam, "simul", "@isPlaying")
  /** the layers which are already expanded are saved, so that we do  not need to expand them again from one run to the next */
  var expandedLayers: Set[String] = fromXMLasList((displayParam \\ "expandedLayer").head).toSet

  /** updates the xml containing all the Param of the CAs, for the moment we only save expanded layers, and displayed fields, with their colors
   * we drop the two hexa digit of the alpha component of colors, it is not used */
  private def updateAndSaveXMLparamCA(): Unit = {
    displayParam =
      <displayParam>
        <expandedLayer>
        {expandedLayers.map(nameLayer => <Layer>
          {nameLayer}
        </Layer>)}
      </expandedLayer>
        <colorOfField>
          {colorDisplayedField.keys.map(nameField => {
          val c = colorDisplayedField(nameField) //we and with 0xFFFFFF because we do use the alpha parameter
          <layer color={"0x" + c.getRGB.toHexString.toUpperCase.drop(2)}>
            {nameField}
          </layer>
        })}
        </colorOfField>
      </displayParam>
    XML.save("src/main/scala/" + chosenDir + "/displayParam/" + nameCA + ".xml", displayParam)
  }

  private class SimpleButton(ic: javax.swing.Icon) extends Button() {
    icon = ic
    contents += this
    Controller.this.listenTo(this) //Controller.this refer to the enclsing controller
  }

  private val ForwardButton = new SimpleButton(forwardIcon) //myButton(forwardIcon, this)
  private val InitButton = new SimpleButton(initIcon)
  private val PlayPauseButton = new SimpleButton(if (isPlaying) pauseNormalIcon
  else playNormalIcon)

  //val globalInit: Array[String] = Array("center", "border", "yaxis","random")  //"onCircle", "random", "poisson", "blakHole"

  //Create the combo box, select the item at index 3.
  //Indices start at 0, so 3 specifies blackHole.
  val globalInitList = new ComboBox[String](globalInit) {
    selection.item = globalInit(3)
  }
  contents += globalInitList
  listenTo(globalInitList.selection)


  //todo add a jcombo to select a number between 0 and 9


  /** When we switch mode between pause and play, the icon of the PlayPause button toggles */
  private def togglePlayPauseIcon(): Unit = {
    PlayPauseButton.icon =
      if (isPlaying) pauseNormalIcon
      else playNormalIcon
  }

  peer.setRollover(true)
  disableBinding(peer) //we want to use spacebar and left/right for other purpose than switching buttons in the toolbar
  listenTo(this.keys)
  //listenTo(mouse.clicks)
  reactions += {
    case ExpandLayer(s) =>
      expandedLayers += s
      updateAndSaveXMLparamCA()
      layerTree.hideRoot
      layerTree.repaint()
      mf.pack() //resize the space allocated to the tree so that it prints entirely
    // mf.unmaximize()
    // we hope it recomputes size of tree windows so as to accomodate
    //this.repaint()
    case CollapseLayer(s) =>
      expandedLayers -= s
      updateAndSaveXMLparamCA()
      layerTree.hideRoot
      layerTree.repaint()
      mf.pack()
    case ToggleColorEvent(s) =>
      val l = locusDisplayedOrDirectInitField(s)
      colorDisplayedField =
        if (colorDisplayedField.contains(s)) //we supress a color
        {
          colorDisplayedField -= s
          displayedLocus = colorDisplayedField.keys.map(locusDisplayedOrDirectInitField(_)).toSet + V()
          if (!displayedLocus.contains(l))
            for (env <- envList)
              env.medium.removeLocus(l)
          colorDisplayedField - s
        }
        else { //we add a color
          if (!displayedLocus.contains(l)) //we have a new locus to display
          {
            for (env <- envList)
              env.medium.addNewLocus(l)
            displayedLocus += l
          }
          val mainColorLeft = mainColors.toSet.diff(colorDisplayedField.values.toSet)
          if (mainColorLeft.nonEmpty) {
            var naturalChoice = Math.abs(s.hashCode) % mainColors.length
            while (!mainColorLeft.contains(mainColors(naturalChoice)))
              naturalChoice = (naturalChoice + 1) % mainColors.length //look for the first main color not used yet
            colorDisplayedField + (s -> mainColors(naturalChoice))
          }
          else colorDisplayedField //we could not find a new color, nothing will change
        }
      updateAndSaveXMLparamCA()
      layerTree.hideRoot
      layerTree.repaint()

      repaintEnv()

    case ButtonClicked(PlayPauseButton) | KeyReleased(_, Key.Space, _, _) =>
      isPlaying = !isPlaying
      togglePlayPauseIcon()
      if (isPlaying)
        playEnv() //lauch the threads
    case ButtonClicked(ForwardButton) | KeyReleased(_, Key.Right, _, _) =>
      forwardEnv()
      repaintEnv()
      requestFocus()
    case ButtonClicked(InitButton) | KeyReleased(_, Key.A, _, _) =>
      initEnv()
      repaintEnv()
      requestFocus() //necessary to enable listening to the keys again.
    case SelectionChanged(`globalInitList`) => InitButton.doClick()
  }
  focusable = true
  requestFocus

  private def repaintEnv(): Unit = {
    for (env <- envList)
      env.repaint()
  }

  private def playEnv(): Unit =
    for (env <- envList)
      env.play()

  private def forwardEnv(): Unit =
    for (env <- envList)
      env.forward()

  private def initEnv(): Unit =
    for (env <- envList)
      env.init()
}

import java.awt.Color._
import java.lang.Integer.decode

object Controller {
  /** space and arrows where binded to toolBar browsing, this method let them become available keys for replacing  button clicking */
  def disableBinding(c: JComponent): Unit = {
    val im: InputMap = c.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT)
    for (key <- List("RIGHT", "LEFT", "SPACE")) //keys to be disabled so as to be used for own purpose
      im.put(KeyStroke.getKeyStroke(key), "none")
  }

}

private object colors {
  //primary, secondary and tertiary colors aranged on a "color wheel" which exhibits a toroidal metric.
  private val chartreuseGreen = new Color(decode("0x80FF00"))
  private val springGreen = new Color(decode("0x00FF80"))
  private val azure = new Color(decode("0x0080FF"))
  private val violet = new Color(decode("0x8000FF"))
  private val rose = new Color(decode("0xFF0080"))
  val mainColors: Array[Color] = Array(red, orange, yellow, chartreuseGreen, green, springGreen, cyan, azure, blue, violet, magenta, rose)
  //gray tones are used for fixed system layers such as debug, liveIf,
  val grays: Array[Color] = Array(darkGray, gray, lightGray, white)
}
