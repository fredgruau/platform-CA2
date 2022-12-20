package simulator

import simulator.SimulatorUtil._
import simulator.XMLutilities._
import triangulation.Vector2D
import java.awt.{Color, Polygon}
import java.net.URL
import javax.swing.ImageIcon
import scala.swing.Swing.Icon
import scala.swing._
import scala.xml.Node
import BorderPanel.Position._

object Simulator extends SimpleSwingApplication {
  /** name of Cellular automaton being simulated, to be set by method startUp, and then used by method top */
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

  /** @param args command line argument, contains the name of CA being simulated */
  override def main(args: Array[String]): Unit = {
    super.main(args)
  }

  /** hierarchy of swing Jcomponents */
  def top: MainFrame = new MainFrame {
    title = "spatial computation"
    /** contains XML code representing many parameters */
    val paramCA: Node = readXML("src/main/scala/compiledCA/" + nameCA + "param.xml")
    //  preferredSize = new Dimension(xInt(param,"display","@width"),xInt(param,"display","@height"))
    //size = (1024, 768): Dimension
    val classCA: Class[CAloops] = loadClass("compiledCA." + nameCA)
    /** contains the loops but also many other parameters */
    val progCA: CAloops = getProg(classCA)
    /** process the signal we create controller first in order to instanciate state variable used by tree */
    val controller = new Controller(nameCA, paramCA, progCA)
    /** Tree for browsing the hierarchy of layers and which field to display */
    val layerTree = new LayerTree((paramCA \\ "layers").head, controller)
    val scrollableXmlTree = new ScrollPane(layerTree) //we put it scrollable because it can become big
    controller.init(layerTree) //now we can pass it to the controller which needs to listen to exansion and coloration events
    /** When simulating CAs whose number of Lines and columns augment */
    val sizesCA: collection.Seq[(Int, Int)] = fromXMLasListIntCouple(paramCA, "sizes", "size", "@nbLine", "@nbCol")
    /** We simulate several CA simultaneously. We generate a list of environement using an iterator */
    val iterEnvs: Iterable[Env] = envs(sizesCA, controller)
    /** pannels are put together in a  Grid using the GridBagPannel container, which allows to fill muliple lines */
    val pannels: GridBagPanel = new GridBagPanel {
      /** helper supplying default values for specifying where to put the pannel, and how many columns it will span */
      def constraints(x: Int, y: Int, gridwidth: Int = 1, fill: GridBagPanel.Fill.Value = GridBagPanel.Fill.None): Constraints = {
        val c = new Constraints
        c.gridx = x;
        c.gridy = y
        c.gridwidth = gridwidth;
        c.fill = fill
        c
      }

      var numEnv = 0
      var numCell = 0
      //how many columns
      val nbColPannel: Int = xInt(paramCA, "display", "@nbCol")
      for (env <- iterEnvs) {
        controller.envList = controller.envList :+ env //we will need to acess the list of env, from the controler
        env.pannel = new CApannel(controller.CAwidth, controller.CAheight, env, progCA) // the number of CAlines is 1/ sqrt(2) the number of CA colomns.
        if (sizesCA(numEnv)._2 >= 30) { // if the CA has too many columns, it get displayed on multiple columns
          assert(numCell % nbColPannel == 0, "you must garantee that CA whose number of columns is >=30 are displayed on multiple of nbColPannel")
          add(env.pannel, constraints(numCell % nbColPannel, numCell / nbColPannel, nbColPannel, GridBagPanel.Fill.Horizontal)) //adds the pannel using the Grid layout (GridBagPnnel)
          numCell += nbColPannel
        }
        else { //adds the pannel in a signel cell
          add(env.pannel, constraints(numCell % nbColPannel, numCell / nbColPannel))
          numCell += 1
        }
        numEnv += 1
      }
    }
    val scrollablPannels = new ScrollPane(pannels) // we generate many pannels and the mouse wheel will allow to easily scroll
    /** this way of doing make the toolbar floatable */
    contents = new BorderPanel {
      layout(scrollableXmlTree) = West
      layout(controller) = North
      layout(scrollablPannels) = Center
    }

  }
}

object ExampleData {
  // retrieve  icons stored in the ressources directory
  //  def getIconUrl(path: String): URL = resourceFromClassloader(path) ensuring(_ != null, "Couldn't find icon " + path)
  val fileIcon: ImageIcon = Icon("src/ressources/file.png")
  val folderIcon: ImageIcon = Icon("src/ressources/folder.png")
  val playNormalIcon: ImageIcon = Icon("src/ressources/play_black.gif")
  val pauseNormalIcon: ImageIcon = Icon("src/ressources/pause_black.gif")
  val forwardIcon: ImageIcon = Icon("src/ressources/skip_forward_black.gif")
  val backwarddIcon: ImageIcon = Icon("src/ressources/skip_backward_black.gif")
  val initIcon: ImageIcon = Icon("src/ressources/rewind_black.gif")
}

object SimulatorUtil {
  /**
   *
   * @param sizes      the different posible CA sizes
   * @param controller the controler
   * @return we generates  the env Iterator in a separate method because it is big
   */
  def envs(sizes: collection.Seq[(Int, Int)], controller: Controller): Iterable[Env] = {
    val param = controller.paramCA
    new Iterable[Env] {
      val iterator: Iterator[Env] = new Iterator[Env] {
        var nbIter = 0 //counter
        /** the parameter on which we iterate */
        val iter: String = x(param, "display", "@iter") //what we iterate on
        /** coded as a double so that we do not loose precision when multiplying by sqrt(2) */
        var nbLineCA: Int = xInt(param, "machine", "@nbLine")
        var nbColCA: Int = xInt(param, "machine", "@nbCol")
        /** coded as a method because when iterating through the CAsizes, nbColCA is modified */
        val arch: String = x(param, "machine", "@arch")

        /** @return `true` if there is a next element, `false` otherwise */
        override def hasNext: Boolean = iter match {
          case "CAsize" => nbIter < sizes.size
        }

        /** @return next element */
        override def next(): Env = {
          iter match {
            case "CAsize" => nbLineCA = sizes(nbIter)._1; nbColCA = sizes(nbIter)._2
          } //inital value of nbLineCA
          nbIter = nbIter + 1
          new Env(arch, nbLineCA, nbColCA, controller, 0)
        }
      }
    }
  }

  /**
   *
   * @param path where to find a compiledCA */
  def loadClass(path: String): Class[CAloops] = {
    var res: Class[CAloops] = null;
    try {
      res = Class.forName(path).asInstanceOf[Class[CAloops]];
    }
    catch {
      case e: ClassNotFoundException =>
        System.out.println("la classe " + path + " n'existe même pas");
    }
    return res;
  }

  def getProg(progClass: Class[CAloops]): CAloops = {
    var res: CAloops = null
    try res = progClass.newInstance
    catch {
      case e: InstantiationException =>
        e.printStackTrace()
      case e: IllegalAccessException =>
        e.printStackTrace()
    }
    res
  }
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

