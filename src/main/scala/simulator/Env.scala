package simulator

import compiler.ASTB.False
import compiler.Locus
import triangulation.Utility.halve
import triangulation.{Init, Medium}

import scala.collection.JavaConverters._
import java.awt.Color
import java.lang.Thread.sleep
import scala.collection.convert.ImplicitConversions.`map AsScala`
import scala.collection.immutable.HashMap
import scala.collection.mutable
import scala.util.Random

/**
 * contains all the information needed to run a given CA.
 *
 * @param nbColCA    number of column in the CA grid
 * @param nbLineCA   number of lines in the CA grid
 * @param controller the controller contians information valid for all the environment
 * @param initName   init method for root layer, which can vary
 * @param randomRoot so that we can reproduce same list of random numbers
 */
class Env(arch: String, nbLineCA: Int, val nbColCA: Int, val controller: Controller, initName: HashMap[String, String],
          val randomRoot: Integer) {
  /** current time */
  var t = 0
  /** Random number generator */
  var rand: Random = new Random(randomRoot)
  /** contains a thread which iterates the CA, while not asked to pause */

  val medium: Medium = arch match {
    case "christal" => Medium(nbLineCA, nbColCA, controller.CAwidth, this) //default medium is christal
  }
  /** Memory of the CA, it is being rewritten by the running thread, not touched if being displayed
   * we add 1 to the column size  medium.nbInt32CAmem +1 so as to avoid catching ArrayIndexOutOfBoundsException
   * when  we write at i+1 instead of i, (we do that in order to avoid memorizing register introudced for tm1s, and save local memory */
  val mem: Array[Array[Int]] = Array.ofDim[Int](controller.progCA.CAmemWidth(), medium.nbInt32CAmem + 1)

  /** associated pannel */
  var pannel: CApannel = null //to be set latter due to mutual recursive definition

  //init() // this initialization is to be called after creation, because pannes cannot be set at creation
  // at runtime, when the user restarts the whole simulation from the restart button


  /**
   * The memory is set back to virgin
   */
  private def resetMem(): Unit =
    for (bitPlane <- mem)
      for (i <- 0 until bitPlane.length)
        bitPlane(i) = 0;
  /** visit all layers that should be initialized directly,  and init the layers using the designated initMethod */
  private def initMemCA(): Unit = {
    //for (layerName: String <- controller.progCA.directInit()) {
    resetMem()
    for (layerName: String <- controller.progCA.init().keys) { //iterate over the layers to be initalized
      /** fields layerName's components */
      val memFields2Init: Seq[Array[Int]] = memFields(layerName) //gets the memory plane
      val initNameFinal = initName.getOrElse(layerName, controller.initName(layerName)) //either it is the root layer or we find it in env
      val initMethod: Init = medium.initSelect(initNameFinal, controller.locusOfDisplayedOrDirectInitField(layerName))
      initMethod.init(memFields2Init.toArray) //we pass the locus here, several init are reused with different locus, such as def/center/yaxis
    }
  }

  def init(): Unit = {
    rand = new Random(randomRoot) //we reinitialize the random number in order to reproduce exactly the same random sequence
    initMemCA() //invariant stipulates that memory should be filled so we fill it already right when we create it
    controller.progCA.copyLayer(mem)
    if (medium.voronoi.isEmpty)
      medium.initVoronoi(controller.displayedLocus) //we have to compute the voronoi upon medium's creation
    for (_ <- 0 until controller.t0) //forward till to
      forward()
    computeVoronoirColors() // for the initial painting
    repaint() //  cannot be called now, because the associated pannel has not been created yet.
    if (controller.isPlaying) //lauch the threads
      play()
  }

  /**
   *
   * @param fieldName name of a field that we want to read in CA memory
   * @return a list of array of Int32  storing the  field components
   */
  def memFields(fieldName: String): List[Array[Int]] =
    controller.memFieldsOffset(fieldName).map(mem(_))

  /** iterate through all the layers to be displayed */
  private def computeVoronoirColors(): Unit = {
    medium.resetColorVoronoi(controller.displayedLocus)
    for ((layerName, color) <- controller.colorDisplayedField) { //process fiedls to be displayed, one by one
      val locus: Locus = controller.locusOfDisplayedOrDirectInitField(layerName)
      val bitSize: Int = controller.bitSizeDisplayedOrDirectInitField.getOrElse(layerName, 1) //default bitsize is one, for boolean
      val bitPlane: List[Array[Int]] = memFields(layerName)
      val density = locus.density * bitSize
      var colorAjusted: Color = if (bitSize > 1) color else halve(color) //if we print int, we have to make a sum of colors, so we first take halve
      assert(density == bitPlane.size, "the number of bit plane should be equal to the field's density")
      for (i <- 0 until bitSize) { //we decompose an int into its bits
        medium.sumColorVoronoi(locus, colorAjusted, bitPlane.slice(i * locus.density, (i + 1) * locus.density))
        colorAjusted = halve(colorAjusted)
      }
    }
  }

  def play(): Unit = {
    val thread = new Thread {
      override def run(): Unit = {
        while (controller.isPlaying) //no pause asked by the user, no bugs detected
        {
          forward()
          if (bugs.size > 0) controller.isPlaying = false
          repaint()
          sleep(50) // slow the loop down a bit
        }
      }
    }
    thread.start()
  }


  var bugs: mutable.Buffer[String] = mutable.Buffer.empty

  /** does one CA iteration on the memory */
  def forward(): Unit = {
    //  controller.progCA.anchorFieldInMem(mem) //todo a refaire seulement si meme change (quand on display ou qu'on display plus)
    bugs = controller.progCA.theLoops(medium.propagate4Shift, mem).asScala //we retrieve wether there was a bug
    t += 1
  }

  def repaint(): Unit = {
    computeVoronoirColors()
    pannel.repaint()
  }

}
