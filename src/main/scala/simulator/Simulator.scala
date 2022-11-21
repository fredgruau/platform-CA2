package simulator

import java.awt.Polygon

import compiler.Locus
import simulator.DynamicClassUtility._
import triangulation.{Medium, Vector2D}

import scala.collection.JavaConverters._
import scala.collection.immutable.HashMap
import scala.swing.Swing.{Icon, pair2Dimension}
import scala.swing._
import java.awt.Color
import java.net.URL

import javax.swing.{Icon, ImageIcon}
import simulator.Simulator.CAtype.CAMem
import simulator.XMLutilities.{xInt, _}

import scala.xml.Node

object Simulator extends SimpleSwingApplication {
  /** name of Cellular automaton being simulated */
  var nameCA: String = " "

  /**
   * startup is called before top is launched,so that
   * it can access the nameCA and store it in order to open the appropriate files
   *
   * @param args command line argument, contains the name of CA being simulated
   */
  override def startup(args: Array[String]): Unit = {
    nameCA = args(0)
    super.startup(args)
  }

  /**
   *
   * @param args command line argument, contains the name of CA being simulated
   */
  override def main(args: Array[String]): Unit = {
    super.main(args)
  }


  /**
   *
   * @param param      contains parameters
   * @param sizes      the different posible CA sizes
   * @param CAwidth    how many pixelx in width are available
   * @param CAmemWidth how many memory bit planes in the CA
   * @param controller the controler
   * @return we generates all the env in a separate method because it is big
   */
  def envs(param: Node, sizes: collection.Seq[(Int, Int)], CAwidth: Int, CAmemWidth: Int, controller: Controller): Iterable[Env] = {
    /**
     *
     * @param CAmemWidth total number of Int32 needed to compute the CA's next state, including system bits such as bug
     * @return the number of Int32 needed for one bit plan of the CA memory
     */
    def CAmemNbInt32(CAmemWidth: Int, nbLineCA: Int, nbColCA: Int): Int = {
      if (nbColCA <= 30) { //one int32 stores one or several sub= line, encoded on 30 of its bits
        val nbSubLines = 30 / (nbColCA) //two bits are devoted to communication
        (nbLineCA / nbSubLines).toInt
      }
      else { //symetric case: we need nbInt32 ints, to store one line of the CA
        val nbInt32 = nbColCA / 30
        (nbLineCA * nbInt32).toInt
      }
    }

    new Iterable[Env] {
      val iterator: Iterator[Env] = new Iterator[Env] {
        var nbIter = 0 //counter
        /** the parameter on which we iterate */
        val iter = x(param, "display", "@iter") //what we iterate on
        /** coded as a double so that we do not loose precision when multiplying by sqrt(2) */
        var nbLineCA: Int = xInt(param, "machine", "@nbLine")
        var nbColCA: Int = xInt(param, "machine", "@nbCol")
        /** coded as a method because when iterating through the CAsizes, nbColCA is modified */
        val arch = x(param, "machine", "@arch")
        //Set the initial values of environment when iterating: it also depend on what we iterates
        iter match {
          case "CAsize" =>
            nbLineCA = sizes(0)._1 //inital value of nbLineCA
            nbColCA = sizes(0)._2
        }

        override def hasNext: Boolean = iter match {
          case "CAsize" =>
            nbIter < sizes.size
        }

        override def next(): Env = {
          iter match {
            case "CAsize" =>
              nbLineCA = sizes(nbIter)._1 //inital value of nbLineCA
              nbColCA = sizes(nbIter)._2
              nbIter = nbIter + 1
          }
          new Env(arch, nbLineCA, nbColCA, CAwidth, controller,
            Array.ofDim[Int](CAmemWidth, CAmemNbInt32(CAmemWidth, nbLineCA, nbColCA)), 0)
        }
      }
    }
  }


  def myButton(ic: Icon, controller: Controller) = new Button {
    icon = ic
    controller.listenTo(this)
  }


  /** hierarchy of swing widget */
  def top: MainFrame = new MainFrame {
    title = "spatial computation"
    val param: Node = readXML("src/main/scala/compiledCA/" + nameCA + "param.xml")
    //  preferredSize = new Dimension(xInt(param,"display","@width"),xInt(param,"display","@height"))
    //size = (1024, 768): Dimension
    val classCA: Class[CAloops] = loadClass("compiledCA." + nameCA)
    val progCA: CAloops = getProg(classCA)

    def CAmemWidth = progCA.CAmemWidth() //shortcut that increases lisibility
    /** process the signal we create controller first in order to instanciate state variable used by tree */
    val controller = new Controller(nameCA, param, progCA)
    val xmLayerHierarchy: Node = readXML("src/main/scala/compiledCA/" + nameCA + "layer.xml")
    /** Tree for browsing the hierarchy of layers and which field to display */
    val layerTree = new LayerTree(xmLayerHierarchy, controller)
    val scrollableXmlTree = new ScrollPane(layerTree) //we put it scrollable because it can become big
    controller.init(layerTree)

    /** this is for the display, this is not the number of lines and columns. */
    val CAwidth = xInt(param, "display", "@CAwidth")
    val CAheight = xInt(param, "display", "@CAheight")
    val sizes: collection.Seq[(Int, Int)] = fromXMLasListIntCouple(param, "sizes", "size", "@nbLine", "@nbCol")

    val iterEnvs: Iterable[Env] = envs(param, sizes, CAwidth, CAmemWidth, controller)

    val pannels = new GridBagPanel {
      def constraints(x: Int, y: Int): Constraints = {
        val c = new Constraints;
        c.gridx = x;
        c.gridy = y;
        c
      }

      var numEnv = 0
      val nbColPannel = xInt(param, "display", "@nbCol")

      for (env <- iterEnvs) {
        controller.envList = controller.envList :+ env //we will need to acess the list of env, from the controler
        env.pannel = new CApannel(CAwidth, (CAwidth / Math.sqrt(2)).toInt, env, progCA)
        add(env.pannel, constraints(numEnv % nbColPannel, numEnv / nbColPannel)) //adds the pannel using the Grid layout (GridBagPnnel)
        numEnv += 1
      }
    }
    val scrollablPannels = new ScrollPane(pannels)

    val ForwardButton = myButton(ExampleData.forwardIcon, controller)
    val toolBar = new ToolBar() {
      peer.setRollover(true)
      contents += ForwardButton
    }

    contents = new BorderPanel {

      import BorderPanel.Position._

      layout(scrollableXmlTree) = West
      layout(controller) = East //controller takes O room
      layout(toolBar) = North
      layout(scrollablPannels) = Center
    }
    //contents=new ScrollPane(xmlTree)
    // contents= new SplitPane(Orientation.Vertical, new ScrollPane(xmlTree){preferredSize = (1024, 768): Dimension}, new Controller(xmlTree)) {  continuousLayout = true  }
    //This setting allows go insert the contoler as a pannel, without wasting space
    //contents=new FlowPanel{ contents+=new ScrollPane(xmlTree);contents+=controller}
  }

  object ExampleData {
    // File system icons
    def getIconUrl(path: String): URL = resourceFromClassloader(path) ensuring(_ != null, "Couldn't find icon " + path)

    // val fileIcon = Icon(getIconUrl("/scalaswingcontrib/test/images/file.png"))
    //   val folderIcon = Icon(getIconUrl("/scalaswingcontrib/test/images/folder.png"))
    val fileIcon: ImageIcon = Icon("src/ressources/file.png")
    val folderIcon: ImageIcon = Icon("src/ressources/folder.png")
    val playNormalIcon = Icon("src/ressources/play_black.gif")
    val pauseNormalIcon = Icon("src/ressources/pause_black.gif")
    val forwardIcon = Icon("src/ressources/skip_forward_black.gif")
    val backwarddIcon = Icon("src/ressources/skip_backward_black.gif")
  }

  /** contains the types used in the simulator */
  object CAtype {
    /** stores all the memory fields of a CA */
    type CAMem = Array[Array[Int]]
    /** defines the value of one bit for all vertices, or for one subfield of all edges, face or transfer locus */
    type pointLines = Array[Array[Option[Vector2D]]]

    /** allows to reuse the same code for displaying or for generating svg */
    trait myGraphics2D {
      def setColor(c: Color): Unit

      def fillPolygon(p: Polygon): Unit

      def drawPolygon(p: Polygon): Unit
    }

  }
}
