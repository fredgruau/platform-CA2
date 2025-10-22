package simulator

import compiler.ASTB.False
import compiler.Locus.locusV
import compiler.{Locus, V}
import dataStruc.Util.{deepCopyArray, isEqualto, isMiror, printMat}
import simulator.Medium.christal
import simulator.Util.copyBasic
import triangulation.Utility.halve

import scala.collection.JavaConverters._
import java.awt.Color
import java.lang.Thread.sleep
import scala.collection.convert.ImplicitConversions.`map AsScala`
import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.{immutable, mutable}
import scala.swing._
import scala.util.Random

/**
 * contains all the information needed to run a given CA.
 *
 * @param nbCol  number of column in the CA grid
 * @param nbLine number of lines in the CA grid
 * @param controller the controller contians information valid for all the environment
 * @param initName   init method for root layer, which can vary
 * @param randomRoot so that we can reproduce same list of random numbers
 */
class Env(arch: String, nbLine: Int, nbCol: Int, val controller: Controller, initName: HashMap[String, String],val t0:Int) {
  /** current time */
  var t = -1 //incoherent value, should be initialized

  val medium: Medium with encodeByInt with InitSelect = arch match {
    case "christal" => christal(nbLine, nbCol, controller.CAwidth) //default medium is christal
  }
  /** Random number generator each medium has its copy */
  medium.initRandom(controller.randomRoot)
  /** Memory of the CA, it is being rewritten by the running thread, not touched if being displayed
   * we add 1 to the column size  medium.nbInt32CAmem +1 so as to avoid catching ArrayIndexOutOfBoundsException
   * when  we write at i+1 instead of i, (we do that in order to avoid memorizing register introduced for tm1s, and save local memory */
  val mem: Array[Array[Int]] = Array.ofDim[Int](controller.progCA.CAmemWidth(), medium.nbInt32total)
  /** for now we cache only memory config */
  val cache=new dataStruc.Cache[Array[Array[Int]]]
  /** associated pannel */
  var caPannel: CApannel = null //to be set latter due to mutual recursive definition
  val iterationLabel=new Label(""+t)
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
      val finalInitMethodName: String = if (initNameFinal.startsWith(  "global")) controller.globalInitList.selection.item //currently selected init method
      else initNameFinal
      /** if true, negate the ini */
      val inverted=initNameFinal.startsWith(  "globalInv")
      val initMethod: Init = medium.initSelect(finalInitMethodName,
        controller.locusOfDisplayedOrDirectInitField(layerName), // locus is passed. It is used in def/center/yaxis
        controller.bitSizeDisplayedOrDirectInitField.getOrElse(layerName, 1),
        controller.density ,inverted     ) // bitsize  is passed.
      //if(layerName.startsWith("lldefVe"))     println("lldefVe")
      initMethod.init(memFields2Init.toArray)

    }
  }
  /** applies a miror on the initial values of layers */
  def initMiror(): Unit = {
    for (layerName: String <- controller.progCA.init().keys) {
      val memFields2Init: Seq[Array[Int]] = memFields(layerName)
      for (memoryPlane <- memFields2Init) {
        val p = medium.propagate4Shift

        val locus = controller.locusOfDisplayedOrDirectInitField(layerName)
        if(locus == compiler.Locus.locusV && ! layerName.startsWith("lldef")) //lldef are used to detect bugs, therefore they should not undergo preparebits.
        {
           p.mirror(memoryPlane)
           p.prepareBit(memoryPlane)}
          //miror comes before preparebit
       /* if(locus == compiler.Locus.locusV && layerName.startsWith("lldef")){
          val matBool = Array.ofDim[Boolean](nbLine, nbCol)
          medium.decode(memoryPlane, matBool)
          printMat(matBool)
        }*/
        val testMiror = false //to be set to true if you want to test miror
        if (locus == locusV && testMiror) {
          val matBool = Array.ofDim[Boolean](nbLine, nbCol)
          medium.decode(memoryPlane, matBool)
          if (!isMiror(matBool)) throw new Exception("pas is miror dans init env")
        }

      }
    }
  }
  def init(): Unit = {
    medium.initRandom(controller.randomRoot) //we reinitialize the random number in order to reproduce exactly the same random sequence
   // medium.middleClosure(controller.currentProximityLocus)  //alternative way of building quickly voronoi.
     //controller.progCA.copyLayer(mem) plus besoin pisque je fais un forward
    if (medium.theVoronois.isEmpty)
      medium.voronoise(controller.displayedLocus, controller.currentProximityLocus) //we have to compute the voronoi upon medium's creation
    initMemCA() //invariant stipulates that memory should be filled so we fill it already right when we create it
// System.out.println( medium.pointSet(V()).size)
    initMiror()
    t= -1
    cache.reset()
    forward() //we do one forward, so as to be able to show the fields.
    for (_ <- 1 until t0) //forward till to
      forward()
    medium.resetColorTextVoronoi(controller.displayedLocus)
    computeVoronoirColors() // for the initial painting
    //computeVoronoirInt32() // for the initial painting
    repaint() //  cannot be called now, because the associated pannel has not been created yet.
    if (controller.isPlaying) //lauch the threads
      play(true)
  }

  /**
   *
   * @param fieldName name of a field that we want to read in CA memory
   * @return a list of array of Int32  storing the  field components
   */
  def memFields(fieldName: String): List[Array[Int]] =
    controller.memFieldsOffset(fieldName).map(mem(_))


  /** we create that array once and forall to decode memory bit planes */
  private val bitPlaneBuffer: Array[Array[Boolean]] = Array.ofDim[Boolean](nbLine, nbCol)


  /**
   * sum to the colors of locus l, the contribution of bitplanes
   * which can represent a boolean field
   *
   * @param locus     locus where new colors are to be summed
   * @param color     color to be summed
   * @param bitPlanes whether it should be summed
   */
  private def sumColorVoronoi(locus: Locus, color: Color, bitPlanes: List[Array[Int]]): Unit = {
    assert (bitPlanes.size == medium.locusPlane(locus).length, "number of bit planes should be locus density")
    for ((plane, points) <- bitPlanes zip medium.locusPlane(locus)) { //we do a dot iteration simultaneously on pointsPlane, and bitPlane
      //   decodeInterleavRot(nbLineCA, nbColCA, plane, sandBox) //we convert the compact encoding on Int32, into simple booleans
      medium.decode(plane, bitPlaneBuffer) //we convert the compact encoding on Int32, into simple booleans
      medium.sumColorVoronoi(color,bitPlaneBuffer, points, controller.darkness)
    }
  }
  /** computes the index of the text that should be displayed */
  private def sumInt32Voronoi(locus: Locus, bitPlanes: List[Array[Int]]): Unit = {
    assert (bitPlanes.size == medium.locusPlane(locus).length, "number of bit planes should be locus density")
    for ((plane, points) <- bitPlanes zip medium.locusPlane(locus)) { //we do a dot iteration simultaneously on pointsPlane, and bitPlane
      //   decodeInterleavRot(nbLineCA, nbColCA, plane, sandBox) //we convert the compact encoding on Int32, into simple booleans
      medium.decode(plane, bitPlaneBuffer) //we convert the compact encoding on Int32, into simple booleans
      medium.sumBitVoronoi(bitPlaneBuffer, points)
    }
  }

  /** computes the text associated to an int32 on each voronoi */
  private def textify(locus: Locus, ls:List[String]): Unit = {
     for (points <- medium.locusPlane(locus))   medium.textify( points,ls)
  }

  /** iterate through all the layers to be displayed */
  private def computeVoronoirColors(): Unit = {

    medium.resetColorTextVoronoi(controller.displayedLocus) //hyper important, poil au dents
    for ((layerName, color) <- controller.colorDisplayedField) { //process fiedls to be displayed, one by one
      val locus: Locus = controller.locusOfDisplayedOrDirectInitField(layerName)
      val bitSize: Int = controller.bitSizeDisplayedOrDirectInitField.getOrElse(layerName, 1) //default bitsize is one, for boolean
      /** 1D array of  integers reprensenting the fields */
      val bitPlane: Array[Array[Int]] = memFields(layerName).toArray
      val density = locus.density * bitSize
      /** if we display an int, then color associated to the field shoudl be halved */
      var colorAjusted: Color = if (bitSize > 1) halve(color) else color //if we print int, we have to make a sum of colors, so we first take halve
      assert(density == bitPlane.size, "the number of bit plane should be equal to the field's density")
      for (i <- (0 until bitSize).reverse) { //loops over the bits of integers reverse so that bit 0 gets smallest color
        //we decompose an int into its  bits, first bit are strongest bit
        /** bitiof locus's arity is locus density */
        val bitiOfLocus: List[Array[Int]] = (0 until locus.density).map(j => bitPlane(i + j * bitSize)).toList

        if(controller.displayedAsText.contains(layerName))   sumInt32Voronoi(locus,  bitiOfLocus)
        else sumColorVoronoi(locus, colorAjusted, bitiOfLocus) // on est ramené au cas d'afficher un  boolV
        colorAjusted = halve(colorAjusted)// on divise par deux pour arriver au bit de point moins fort.
      }
      //for text we have to compute a string on each voronoi, the default case uses a list of string
      if(controller.textOfFields.contains(layerName))
            textify(locus,controller.textOfFields(layerName))
    }
  }


  /** contains a thread which iterates the CA, while not asked to pause */
  def play(fwd:Boolean): Unit = {
    val thread = new Thread {
      override def run(): Unit = {
        while (controller.isPlaying) //no pause asked by the user, no bugs detected
        { var nbIter = 0;
          val nbLoops=math.pow(2,controller.speedSlider.value)
          while (controller.isPlaying && nbIter < nbLoops ) // display every 2^speedSlider.value
          {if(fwd) forward() else backward(1);
            nbIter+=1
            if (bugs.size > 0)
              controller.isPlaying = false;
          }
          repaint(); sleep(50);
          // // slows down the loop  a bit
        }

      }
    }
    thread.start()
  }


  var bugs: mutable.Buffer[String] = mutable.Buffer.empty
  /** contains locus of bug */
  var lociBug:Set[Locus]=immutable.HashSet()
  /** does one CA iteration on the memory */
  def forward(): Unit = {
    //  controller.progCA.anchorFieldInMem(mem) //todo a refaire seulement si meme change (quand on display ou qu'on display plus)
    bugs = controller.progCA.theLoops(medium.propagate4Shift, mem).asScala //we retrieve wether there was a bug
    t += 1
    if (bugs.nonEmpty) {  //we set the locus of bugs
      for(bugName<-bugs) {
       val  locusBug=controller.progCA.fieldLocus.asScala(bugName)
       lociBug=lociBug+locusBug // pas sur qu'on doive pas plutot stoquer cela dans env
        val BugFieldName = "llbug"+locusBug.toString.dropRight(2)
        controller.colorDisplayedField+=(BugFieldName->Color.white)
              }
      controller.checkNewLocus(lociBug) //marche meme si y a plusieurs bug différent détecté en meme temps.
      val i=0
    }
    iterationLabel.text="" + t
    cache.push(deepCopyArray( mem))
  }

  /** @param nbIter number of iteration steps
   * does backward steps using the cache */
  def backward(nbIter:Int): Unit = {
    // bugs = controller.progCA.theLoops(medium.propagate4Shift, mem).asScala //we retrieve wether there was a bug
    if(cache.top==null) return; //on backward pas sur la config initiale
    val timeTarget=t-nbIter
    copyBasic(cache.pop(nbIter),mem)
    t = cache.nextIndex-1
    while(t<timeTarget) //forward till to
      forward()
  }

  /** permet d'aller plus vite en arriére presque le meme code que backward, car "cache" peut prendre en parametre,
   *  le nombre d'itération que l'on souhaite reculer*/
  def fastBackward(nbIter:Int): Unit ={
    if(cache.top==null) return;
     copyBasic(cache.pop(nbIter),mem)
    t = cache.nextIndex
    iterationLabel.text="" + t
  }

  /** permet d'aller plus vite au résultat sans se taper de voir un tas d'image */
  def fastForward(nbIter:Int)=
    for(i<- 0 until nbIter) forward()

  def repaint(): Unit = {
    computeVoronoirColors()
    caPannel.revalidate()
    caPannel.repaint()

  }

}
