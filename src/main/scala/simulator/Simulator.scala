package simulator

import simulator.SimulatorUtil._
import simulator.XMLutilities._
import triangulation.Vector2D

import java.awt.{Color, Polygon}
import java.io.{FileNotFoundException, IOException}
import java.net.URL
import javax.swing.{ImageIcon, JTree}
import scala.swing.Swing.Icon
import scala.swing._
import scala.xml.{Elem, Node}
import BorderPanel.Position._
import scala.collection.immutable.HashMap

object Simulator extends SimpleSwingApplication {
  /** name of Cellular automaton being simulated, to be set by method startUp, and then used by method top */
  var nameCA: String = " "
  /** parameters defining sizes, t0, isPlaying, common to all simulations */
  var simulParam: Node = null
  /** contains info about which layers are expanded, what where the already  used colors. */
  var displayParam: Node = null
  var globalInit: Node = null
  var selectedGlobalInit: Int = -1 //it will bug if we forget to read it.
  var nameGlobalInit: String = null
  /**
   * @param args command line argument, contains the name of CA being simulated
   *             startup is called before top is launched,so that
   *             it can access args which nameCA as well as other names of files containing parameters for simulation
   *             and store them in order to later be able to open the files with the CA program, and parameters
   */
  override def startup(args: Array[String]): Unit = {
    nameCA = args(0) //name of the CA program
    nameGlobalInit = args(1)
    globalInit = readXML("src/main/scala/compiledCA/globalInit/" + nameGlobalInit)
    val nameSimulParam = args(2)
    simulParam = readXML("src/main/scala/compiledCA/simulParam/" + nameSimulParam)
    displayParam = try {
      readXML("src/main/scala/compiledCA/displayParam/" + nameCA + ".xml")
    }
    catch {
      case _: FileNotFoundException => readXML("src/main/scala/compiledCA/displayParam/default.xml")
    }


    super.startup(args)
  }

  /** @param args command line argument, contains the name of CA being simulated */
  override def main(args: Array[String]): Unit = {
    super.main(args)
  }

  /** hierarchy of swing Jcomponents */
  def top: MainFrame = new MainFrame {


    /** possible directories where CA can be found */
    val directories = List("compiledCA") //, "compHandCA")
    //find  the right directory
    val possibleDir = directories.filter((s: String) => loadClass(s + "." + nameCA) != null)
    assert(possibleDir.size > 0, nameCA + "could not be found in any of the directories " + directories)
    assert(possibleDir.size < 2, nameCA + "could  be found two times in the directories " + directories)
    val chosenDir: String = possibleDir.head //we take the first found directory
    val classCA: Class[CAloops2] = loadClass(chosenDir + "." + nameCA)
    /** contains the loops but also many other parameters */
    val progCA: CAloops2 = getProg(classCA) //will be used to create the controller, but also the browsable treeLayers.
    title = "spatial computation " + nameCA + " gateCount=" + progCA.gateCount() + " memory Width=" + progCA.CAmemWidth()


    /** process the signal we create controller first in order to instanciate state variable used by layerTree */
    val controller = new Controller(nameCA, globalInit, nameGlobalInit, simulParam, displayParam, progCA, chosenDir, this)
    /** Tree for browsing the hierarchy of layers and which field to display */
    val xmlLayerTree: Elem = readXmlTree(progCA.displayableLayerHierarchy())
    System.out.println("the displayable layers are\n" + xmlLayerTree)
    //creation of layerTree needs controller, in order to be able to send signal of expansion and coloring/uncoloring
    val layerTree: LayerTree = new LayerTree(xmlLayerTree, controller)
    val scrollableXmlTree = new ScrollPane(layerTree) //we put it scrollable because it can become big, when many fields can potentially get displayed
    controller.init(layerTree) //now we can pass it to the controller which needs to listen to expansion and coloration events

    /** We simulate several CA simultaneously. We generate a list of environement using an iterator */
    val iterEnvs: Iterable[Env] = envs(controller)
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

      var numEnv = 0;
      var numCell = 0
      //how many columns
      val nbColPannel: Int = xInt(simulParam, "display", "@nbCol")
      for (env: Env <- iterEnvs) { //effectivement, lorsque on crée les envs, il n'ont as encore leur pannel
        controller.envList = controller.envList :+ env //we will need to acess the list of env, from the controler
        env.pannel = new CApannel(controller.CAwidth, controller.CAheight, env, progCA) // the number of CAlines is 1/ sqrt(2) the number of CA colomns.
        if (env.medium.nbCol >= 30) { // if the CA has too many columns, it get displayed on multiple columns
          assert(numCell % nbColPannel == 0, "you must garantee that CA whose number of columns is >=30 are displayed on multiple of nbColPannel")
          add(env.pannel, constraints(numCell % nbColPannel, numCell / nbColPannel, nbColPannel, GridBagPanel.Fill.Horizontal)) //adds the pannel using the Grid layout (GridBagPnnel)
          numCell += nbColPannel
        }
        else {
          add(env.pannel, constraints(numCell % nbColPannel, numCell / nbColPannel)) //adds the pannel in a single cell
          numCell += 1
        }; numEnv += 1
        // controller.progCA.anchorFieldInMem(env.mem)
        //should be env.init
        //controller.progCA.initLayer(env.mem)
        env.init() // could not be done in the creation of the env, because pannel was not create yet
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

/**
 * retrieve  icons stored in the ressources directory
 */
object ExampleData {
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
   * @param gridSizes  the different posible CA sizes
   * @param controller the controler
   * @return env Iterator implemented  separately  method because it is big
   */
  def envs(controller: Controller): Iterable[Env] = {
    val simulParam = controller.simulParam
    /** When simulating CAs whose number of Lines and columns augment */
    val gridSizes: collection.Seq[(Int, Int)] = fromXMLasListIntCouple(simulParam, "sizes", "size", "@nbLine", "@nbCol")
    /** When simulating CAs with different init */
    val multiInits = xArrayString(simulParam, "multiInit", "@inits")
    val rootLayer: String = if (multiInits.nonEmpty) x(simulParam, "multiInit", "@layer") else null
    val iter: String = x(simulParam, "display", "@iter") //what we iterate on

    def totalIter: Int = iter match {
      case "CAsize" => gridSizes.size
      case "multiInit" => multiInits.size
      case "random" => 4
      case "none" => 1
    }

    new Iterable[Env] {
      val iterator: Iterator[Env] = new Iterator[Env] {
        var nbIter = 0 //counter
        /** the parameter on which we iterate */

        /** coded as a double so that we do not loose precision when multiplying by sqrt(2) */
        var nbLineCA: Int = xInt(simulParam, "machine", "@nbLine")
        var nbColCA: Int = xInt(simulParam, "machine", "@nbCol")
        var initRoot: HashMap[String, String] = HashMap.empty
        /** coded as a method because when iterating through the CAsizes, nbColCA is modified */
        val arch: String = x(simulParam, "machine", "@arch")


        /** @return `true` if there is a next element, `false` otherwise */
        override def hasNext: Boolean = nbIter < totalIter

        /** @return next element */
        override def next(): Env = {
          iter match {
            case "CAsize" => nbLineCA = gridSizes(nbIter)._1; nbColCA = gridSizes(nbIter)._2
            case "multiInit" => initRoot = HashMap(rootLayer -> multiInits(nbIter))
            case "random" => controller.randomRoot = nbIter
            case _ =>
          } //inital value of nbLineCA
          nbIter = nbIter + 1
          new Env(arch, nbLineCA, nbColCA, controller, initRoot)
        }
      }
    }
  }

  /**
   *
   * @param path where to find a compiledCA */
  def loadClass(path: String): Class[CAloops2] = {
    var res: Class[CAloops2] = null;
    try {
      res = Class.forName(path).asInstanceOf[Class[CAloops2]];
    }
    catch {
      case e: ClassNotFoundException =>
        System.out.println("la classe " + path + " n'existe  pas");
    }
    return res;
  }

  def getProg(progClass: Class[CAloops2]): CAloops2 = {
    var res: CAloops2 = null
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
    /** coordinate for all vertices, or for one subfield of all edges, face or transfer locus
     * points is undefined, if it lies out of the bounding box
     * coordinates of the 2D arrays range between nbLine and nbCol */
    type pointLines = Array[Array[Option[Vector2D]]]

    /** allows to reuse the same code for displaying or for generating svg */
    trait myGraphics2D {
      def setColor(c: Color): Unit

      def drawPoint(x: Int, y: Int): Unit

      def fillPolygon(p: Polygon): Unit

      def drawPolygon(p: Polygon): Unit

      def drawText(s: String, i: Int, j: Int): Unit

    }

  }

