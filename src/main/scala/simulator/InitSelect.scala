package simulator

import compiler.{Locus, V}
import triangulation.Vector2D

import scala.util.Random


trait Init {
  /**
   * fills the set of memory fields corresponding to a CA field, according to a given init wished for
   *
   * @param CAmemFields memory fields to fill
   */
  def init(CAmemFields: Array[Array[Int]]): Unit

}

/** for a medium, adds  the possibity of choosing an init */
trait InitSelect {
  self: Medium with encodeByInt=>   // Some inits are using encode

  /**
   *
   * @param initMethodName name of the init chosen
   * @param l              Locus of the layer to be initalized we do not need to pass a bit size, since integer field are usually initialized to zero
   * @return an  "Init" which can initialize a layer, because of lazy, this init is created once and then reused
   *         this is the only public method provided by the initSelect trait,
   */
  def initSelect(initMethodName: String, l: Locus, nbit: Int): Init = {
    initMethodName match {
      case "0" => zeroInit
      case "true" => unInit
      case "center" => centerInit
      case "points" => pointsInit
      case "debug" => zeroInit
      case "sparse" => sparseInitInside(l, nbit)
      case "randinside" => randInitInside(l, nbit)
      case "def" => defInit(l) //here we must take into account the locus, we use a method instead of a lazy val in order to save space
      case "xaxis" => xaxisInit
      case "yaxis" => yaxisInit
      case "dottedBorder" => dottedBorderInit
      case "border" => borderInit
      case "random" => randomInit
      case "false" => zeroInit
    }
  }
  /** Random number generator each medium has its copy */
  private var  rand:Random =null
  def initRandom(r:Int):Unit=rand=new Random(r)
  //geometric primitive fields used to construct initial configurations
  private val origin = new Vector2D(0, 0)
  private val center = new Vector2D(nbLine / 2, nbCol / 2)

  /** different possible inits, non static fields of the medium class, because they use data from the mediium
   * be it only the number of lines and columns.
   * declared with lazy to spare memory, since only one or two will be instanciated
   * make use of primitives fields declared in medium to simplify the programming
   * todo  there is a pb in that we need different init field, in case of random init.=> no val
   *
   * contains material for creating "Init" object which can initialize a layer
   * sub class of medium because for amorphous medium we will need to access the topology of the medium
   *
   * @param locus locus of field being initialized
   * @param nbit  equals to 1 now, could be allowed to become >1 if we make Init for integer layer.
   */

  private lazy val yaxisInit: InitMaald = new InitMaald(1) {
    for (i <- 0 until nbLine) setBoolVField(i, 0)
  }
  private lazy val xaxisInit: InitMaald = new InitMaald(1) {
    for (j <- 0 until nbCol) setBoolVField(0, j)
  }
  private lazy val zeroInit: InitMaald = new InitMaald(1) {} //nothing to do, the boolV field would be zero by default.
  private lazy val unInit: InitMaald = new InitMaald(1) {
    for (i <- 2 until nbLine - 2) {
      val (j0, j1) = if (i % 2 == 0) (2, nbCol - 1) else (1, nbCol - 2)
      for (j <- j0 until j1) {
        boolVField(i)(j) = true

      }
    }
  } //n
  private lazy val dottedBorderInit: InitMold = new InitMold(V(), 1) {
    for (i <- 0 until nbLine) if (i % 2 == 0) {
      setBoolVField(i, 0);
      setBoolVField(i, nbCol - 1)
    }
    for (i <- 0 until nbCol) if (i % 2 == 0) {
      setBoolVField(0, i);
      setBoolVField(nbLine - 1, i)
    }
  }
  private lazy val borderInit: InitMaald = new InitMaald(1) {
    for (i <- 0 until nbLine) {
      setBoolVField(i, 0); setBoolVField(i, nbCol - 1)
    }
    for (i <- 0 until nbCol) {
      setBoolVField(0, i); setBoolVField(nbLine - 1, i)
    }
  }
  private lazy val randomInit: InitMold = new InitMold(V(), 1) {
    override def init(CAmemFields: Array[Array[Int]]): Unit = { // init is redefined becase instead of encode, we directly write into the CA
      for (lCAmem: Array[Int] <- CAmemFields) { //dot iteration, we iterate on the dot product of the two ranges
        for (i <- 0 until lCAmem.size) lCAmem(i) = rand.nextInt()
      }
    }
  }

  /** the def fields have to be generated for each locus. Hence, it is computed on the fly, in order to save memory */
  private def defInit(l: Locus): Init = new InitMold(l, 1) {
    for (d <- 0 until l.density)
      for (i <- 0 until nbLine)
        for (j <- 0 until nbCol)
          if (locusPlane(l)(d)(i)(j).isDefined)
            setMemField(d, i, j)
  }

  /** does a random init covering only cells which will not be mirored */
  private def randInitInside(l: Locus, nbit: Int): Init = new InitMold(l, nbit) {
    for (f <- memFields)
      for (i <- 2 until nbLine - 2) {
        val (j0, j1) = if (i % 2 == 0) (2, nbCol - 1) else (1, nbCol - 2)
        for (j <- j0 until j1) {
          if (rand.nextFloat() < 0.6) //locusPlane(l)(d)(i)(j).isDefined)
            f(i)(j) = true
        }
        //setMemField(f, i, j)
      }
  }

  /** does a sparse init covering only cells which will not be mirored */
  private def sparseInitInside(l: Locus, nbit: Int): Init = new InitMold(l, nbit) {
    for (f <- memFields)
      for (i <- 2 until nbLine - 2) {
        val (j0, j1) = if (i % 2 == 0) (2, nbCol - 1) else (1, nbCol - 2)
        for (j <- j0 until j1) {
          if (rand.nextFloat() < 0.15) //locusPlane(l)(d)(i)(j).isDefined)
            f(i)(j) = true
        }
        //setMemField(f, i, j)
      }
  }

  /** contains material used for InitMaald */
  trait BoolVField {
    /** represent the initial value of a boolV field */
    val boolVField: Array[Array[Boolean]] = Array.ofDim[Boolean](nbLine, nbCol)

    /**
     * @param p a point within the medium
     *          initialize the corresponding value of the boolVfield
     */
    def setBoolVField(p: Vector2D): Unit = setBoolVField(p.x.toInt, p.y.toInt)

    def setBoolVField(i: Int, j: Int): Unit = boolVField(i)(j) = true
  }

  /** initalize all the scalar component of a locus in the same way */
  private class InitMaald(val nbit: Int) extends Init with BoolVField {
    assert(nbit == 1, "InitMaald initialize only boolean fields")

    /** fills the set of memory fields corresponding to a CA field, according to a given init wished for
     *
     * @param CAmemFields memory fields to fill
     */
    override def init(CAmemFields: Array[Array[Int]]): Unit = {
      for (lCAmem: Array[Int] <- CAmemFields) { //dot iteration, we iterate on the dot product of the two ranges
        encode(boolVField, lCAmem)
      }
    }
  }

  private class InitMold(val locus: Locus, val nbit: Int) extends Init {
    /** use as a tmp list of bool arrays], to more  easily computes the initial values */
    val memFields: Array[Array[Array[Boolean]]] = Array.ofDim[Boolean](locus.density * nbit, nbLine, nbCol)
    /** simplification for the common case which is a boolV field */
    val boolVField: Array[Array[Boolean]] = if (locus == V()) memFields(0) else null

    /**
     * @param CAmemFields memory fields to fill
     *                    fills the set of memory fields corresponding to a CA field, according to a given init wished for
     */
    override def init(CAmemFields: Array[Array[Int]]): Unit = {
      assert(CAmemFields.length == memFields.length, "count of CA bit planes does not corresponds " + CAmemFields.length + " " + memFields.length)
      for ((lCA, lCAmem: Array[Int]) <- memFields zip CAmemFields) { //dot iteration, we iterate on the dot product of the two ranges
        encode(lCA, lCAmem)
      }
    }

    def setMemField(d: Int, i: Int, j: Int): Unit = memFields(d)(i)(j) = true

    def setAllMemField(i: Int, j: Int): Unit = {
      for (f <- memFields)
        f(i)(j) = true
    }

    /**
     *
     * @param p a point within the medium
     * @return set the corresponding value of the boolVfield being initialized
     */
    def setAllMemField(p: Vector2D): Unit = setAllMemField(p.x.toInt, p.y.toInt)

    /**
     *
     * @param p a point within the medium
     * @return set the corresponding value of the boolVfield being initialized
     */
    def setBoolVField(p: Vector2D): Unit = setBoolVField(p.x.toInt, p.y.toInt)

    def setBoolVField(i: Int, j: Int): Unit = boolVField(i)(j) = true


  }

  private lazy val centerInit: InitMaald = new InitMaald(1) {
    setBoolVField(center)
  }
  private lazy val pointsInit: InitMaald = new InitMaald(1) {
    setBoolVField(center)
    setBoolVField(center.add(new Vector2D(1, 3)))
    setBoolVField(center.add(new Vector2D(0, -4)))
  }
}
