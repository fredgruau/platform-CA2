package simulator

import java.util
import java.awt.Color
import Simulator.CAtype._
import compiler.Locus
import simulator.XMLutilities.fromXMLasHashMap
import triangulation.{Init, Medium}

import scala.collection.immutable.HashMap
import scala.xml.Node
import scala.collection.JavaConverters._
import triangulation.Utility.halve

/**
 * contains all the information needed to run a given CA.
 *
 * @param nbCol      number of column in the CA grid
 * @param nbLine     number of lines in the CA grid
 * @param controller the controller contians information valid for all the environment
 * @param mem        Memory of the CA, it is being rewritten by the running thread, not touched if being displayed
 * @param randomRoot so that we can reproduce same list of random numbers
 */
class Env(arch: String, nbLine: Int, nbCol: Int, width: Int, val controller: Controller, val mem: CAMem,
          randomRoot: Integer) {

  /** true if the CA's current state is being displayed */
  val beingDisplayed: Boolean = false
  /** contains a thread which iterates the CA, while not asked to pause */
  val thread: Thread = null
  val medium = arch match {
    case "christal" => Medium(nbLine, nbCol, width) //default medium is christal
  }
  /** current time */
  var t = 0
  /** associated pannel */
  var pannel: CApannel = null //to be set latter due to mutual recursive definition
  /** visit all layers that should be initialized directly,  and init the layers using the designated initMethod */
  def initMemCA() = {
    for (layerName: String <- controller.progCA.directInit()) {
      /** fields layerName's components */
      val memFields = controller.memFields(layerName, mem)
      val initMethod: Init = medium.initSelect(controller.initName(layerName))
      initMethod.init(memFields.toArray)
    }
  }


  /** iterate through all the layers to be displayed */
  def computeVoronoirColors() = {
    medium.resetColorVoronoi()
    for ((layerName, color) <- controller.colorDisplayedField) { //process fiedls to be displayed, one by one
      val locus: Locus = controller.locusDisplayedField(layerName)
      val bitSize: Int = controller.bitSizeDisplayedField.getOrElse(layerName, 1) //default bitsize is one, for boolean
      val bitPlane: List[Array[Int]] = controller.memFields(layerName, mem)
      val density = locus.density * bitSize
      var colorAjusted: Color = if (bitSize > 1) color else halve(color)
      assert(density == bitPlane.size, "the number of bit plane should be equal to the field's density")
      for (i <- 0 until bitSize) { //we decompose an int into its bits
        medium.sumColorVoronoi(locus, colorAjusted, bitPlane.slice(i * locus.density, (i + 1) * locus.density))
        colorAjusted = halve(colorAjusted)
      }
    }
  }

  initMemCA() //invariant stipulates that memory should be filled so we fill it already right when we create it
  computeVoronoirColors() // for the initial painting

  override def toString = "CAmem" + mem(0)(0) + "\n"

  def repaint() = {
    computeVoronoirColors()
    pannel.repaint()
  }

}
