package triangulation

import compiler._
import simulator.CAtype.pointLines
import simulator.UtilBitJava.{propagateBit14and1, propagateBit6and1, propagateBitxand1}
import simulator.{PrShift, UtilBitJava}
import triangulation.Medium._
import triangulation.Utility._

import java.awt.Color
import scala.collection.JavaConverters._
import scala.collection.immutable.HashMap
import scala.math.{min, round}
import scala.swing.Dimension
import scala.swing.Swing.pair2Dimension

trait Init {
  /**
   * fills the set of memory fields corresponding to a CA field, according to a given init wished for
   *
   * @param CAmemFields memory fields to fill
   */
  def init(CAmemFields: Array[Array[Int]]): Unit
}

/**
 *
 * Provide a partition in 2D space into polygon, for representing the state of the medium
 * locus are distributed in lines, thus having 2 integer coordinates,
 * vertices are displayed from the start
 * together with a neighborood relationship between locus for computing communication during transfers
 *
 * @param nbColCA     max number of points per line
 * @param nbLineCA    number of lines
 * @param boundingBox Rectangles containing all the points, normally it is also exactly the dimension of the CA pannel.
 * @param vertice     location of the vertices (where the real processing elements are located)
 * @param neighbors   coordinates of the neighbors relative to the center. For the hexagonal it is the same for even (resp. odd)
 *
 */
abstract class Medium(val nbLineCA: Int, val nbColCA: Int, val boundingBox: Dimension, val vertice: pointLines, val neighbors: Array[Array[Array[(Int, Int)]]]) {
  /** number of Int32 needed for the boolean of one bit plane  **/
  def nbInt32: Int

  /** total  number of Int32 needed for one bit plane, including separating integers.   **/
  def nbInt32CAmem: Int

  def propagate4Shift: PrShift

  /**
   * encode from boolean to ints 32 bits
   *
   * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
   * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
   */
  def encode(memCAbool: Array[Array[Boolean]], memCAint32: Array[Int]): Unit

  /**
   * decodes, from Int 32 bits to booleans
   *
   * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
   * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
   */
  def decode(memCAint32: Array[Int], memCAbool: Array[Array[Boolean]]): Unit

  /**
   *
   * @param ni input x coordinate
   * @param nj input y coordinate
   * @return true if the coordinates indicate a point within the cellular automaton
   */
  private def inside(ni: Int, nj: Int) = insideInterval(ni, nbLineCA) && insideInterval(nj, nbColCA)

  /** number of Int32 needed for one bit plan of the CA memory **/
  /*val  nbInt32CAmem  = {
    if (nbColCA < 30) { //one int32 stores one or several sub= line, encoded on 30 of its bits
      assert(30%(nbColCA) == 0 && (nbLineCA * (nbColCA))%30==0,"nbCol is 6 or 14")
      3+ nbInt32 //we need two extra int32 before and one int32 after.
    }
    else { //symetric case: we need nbInt32 ints, to store one line of the CA
      assert( nbColCA%30 == 0,"nbCol is a multiple of 30")
      nbBlock = nbColCA/30 //the number of "macro columns, two if nbColumnx=60"
      nbInt32=(nbLineCA * (nbColCA))/30
      blockSize= nbInt32/nbBlock
      (nbLineCA+1)*nbBlock +2 //we need to insert one integer as a buffer between each macro columns, plus two before and one after
    }
  }*/
  /*val  nbInt32CAmemOld  = {
    if (nbColCA < 30) { //one int32 stores one or several sub= line, encoded on 30 of its bits
      assert(32%(nbColCA+2) == 0 && (nbLineCA * (nbColCA+2))%32==0,"nbCol is 6 or 14")
      3+ nbInt32 //we need two extra int32 before and one int32 after.
    }
    else { //symetric case: we need nbInt32 ints, to store one line of the CA
      assert( nbColCA%30 == 0,"nbCol is a multiple of 30")
      nbBlock = nbColCA/30 //the number of "macro columns, two if nbColumnx=60"
      nbInt32=(nbLineCA * (nbColCA))/30
      blockSize= nbInt32/nbBlock
      (nbLineCA+1)*nbBlock +2 //we need to insert one integer as a buffer between each macro columns, plus two before and one after
    }
  }*/


  /**
   *
   * @param d neighbor index between 0 and 5
   * @param i x coordinate
   * @param j y coordinate
   * @return neighbor in absolute coordinate obtained by adding i,j to the neighbors matrix
   */
  private def neigborsAbs(d: Int, i: Int, j: Int): (Int, Int) = add2(neighbors(d)(i)(j), (i, j))

  /**
   *
   * @param tuple coordinate of a possible point
   * @return that point if the coordinates correspond to a valid point, otherwise, none
   */
  private def tryFind(tuple: (Int, Int)): Option[Vector2D] =
    if (!inside(tuple._1, tuple._2)) None
    else Some(vertice(tuple._1)(tuple._2).get)


  /**
   *
   * @param d neighbor index between 0 and 5
   * @param i x coordinate
   * @param j y coordinate
   * @return the point representing the neighbor edge, if that edge exists
   *         we distinguish the case d<3 in which case the edge can be accessed directly
   *         from the case d=3,4,5 in which case we have to first see if neighbor is defined and if so, take it d-3 edge
   **/
  private def neigborFromEdge(d: Int, i: Int, j: Int) = {
    if (d < 3)
      locusPlane(E())(d)(i)(j)
    else {
      val n = neigborsAbs(d, i, j)
      val p = tryFind(n)
      if (p.isDefined) //the edge does exists
      locusPlane(E())(d - 3)(n._1)(n._2)
      else None
    }
  }


  /** contains points associated to all locus, locus by locus  */
  var locusPlane: HashMap[Locus, Array[pointLines]] = HashMap()
  locusPlane += V() -> Array(vertice) //adds all vertices , its a singleton array because vertice density is only 1.
  locusPlane += E() -> {
    val res = Array.ofDim[Option[Vector2D]](3, nbLineCA, nbColCA)
    for (dir <- 0 until 3) //we consider half of the neighbors first is east, second is northeast, third is nortwest
      for (i <- 0 until nbLineCA)
        for (j <- 0 until nbColCA) {
          val (ni, nj) = neigborsAbs(dir, i, j)
          res(dir)(i)(j) =
            if (!inside(ni, nj))
              None
            else
              Some(vertice(i)(j).get.middle(vertice(ni)(nj).get))
        }
    res
  }
  locusPlane +=
    F() -> {
      val res = Array.ofDim[Option[Vector2D]](2, nbLineCA, nbColCA) //first is down, second is up
      for (dir <- 0 until 2) //we consider half of the neighbors
        for (i <- 0 until nbLineCA)
          for (j <- 0 until nbColCA) {
            val (ni, nj) = neigborsAbs(dir, i, j)
            val (mi, mj) = neigborsAbs(dir + 1, i, j)
            res(dir)(i)(j) =
              if (!inside(ni, nj) || !inside(mi, mj))
                None
              else
                Some(vertice(i)(j).get.add(vertice(ni)(nj).get).add(vertice(mi)(mj).get).mult(0.33333333))
          }
      res
    }
  private val weight = 0.33333 //transfer locus are not located in the middle
  locusPlane +=
    T(V(), E()) -> {
      val res = Array.ofDim[Option[Vector2D]](6, nbLineCA, nbColCA) //first is down, second is up
      for (dir <- 0 until 6) //we consider half of the neighbors
        for (i <- 0 until nbLineCA)
          for (j <- 0 until nbColCA) {
            val eddge = neigborFromEdge(dir, i, j) //the edge we want to consider
            res(dir)(i)(j) =
              if (eddge.isEmpty) None
              else Some(vertice(i)(j).get.mult(weight).add(eddge.get.mult(1 - weight)))
          }
      res
    }

  // todo: mettre tout les locus ladedans!
  /*  addNewLocus(V()) //we add the vertices , by default
    addNewLocus(E())
    addNewLocus(F())
    addNewLocus(F())
    addNewLocus( T(V(),E()))*/
  var triangleSoup: List[Triangle2D] = List()
  /** all the voronoi's polygons plus features */
  var voronoi: HashMap[Vector2D, Voronoi] = HashMap()
  private var displayedPoint: Set[Vector2D] = Set()

  /** Sets the points in space, according to what is being colored */

  def initVoronoi(L: Set[Locus]): Unit = {
    for (l <- L)
      displayedPoint ++= pointSet(l)
    val t = time(voronoise(), "voronoise")
  }


  /**
   * recompute displayed points and voronoi, upon a increase of displayed points
   *
   * @param l new locus asked for coloring;  there was no other colored field of locus l, and now there is
   */
  def addNewLocus(l: Locus): Unit = {
    displayedPoint ++= pointSet(l) //recomputes the displayed point
    val t = time(voronoise(), "voronoise")
  }


  /**
   * recompute displayed points and voronoi, upon a decrease of displayed points
   *
   * @param l locus l is asked for uncoloring, and there is no other colored field of locus l
   */
  def removeLocus(l: Locus): Unit = {
    displayedPoint --= pointSet(l) //recomputes the displayed point
    voronoise()
  }

  /** we create that array once and forall to decode memory bit planes */
  private val sandBox = Array.ofDim[Boolean](nbLineCA, nbColCA)

  def resetColorVoronoi(L: Set[Locus]): Unit =
    for (l <- L)
      for (points2D: pointLines <- locusPlane(l))
        for (i <- 0 until nbLineCA)
          for (j <- 0 until nbColCA) {
            val point = points2D(i)(j) //corresponding point in 2D space
            if (point.isDefined)
              voronoi(point.get).resetColor() //updating voronoi's polygon color
          }

  /**
   * sum to the colors of locus l, the contribution of bitplanes
   * which can represent a boolean field
   *
   * @param locus     locus where new colors will be summed
   * @param color     color to be summed
   * @param bitPlanes where it should be summed
   */
  def sumColorVoronoi(locus: Locus, color: Color, bitPlanes: List[Array[Int]]): Unit = {
    if (bitPlanes.size != locusPlane(locus).length)
      println("the points of the locus must have been generated, and the density must correspond")
    for ((plane, points) <- bitPlanes zip locusPlane(locus)) { //we do a dot iteration simultaneously on pointsPlane, and bitPlane
      //   decodeInterleavRot(nbLineCA, nbColCA, plane, sandBox) //we convert the compact encoding on Int32, into simple booleans
      decode(plane, sandBox) //we convert the compact encoding on Int32, into simple booleans
      for (i <- 0 until nbLineCA)
        for (j <- 0 until nbColCA)
          if (sandBox(i)(j)) { //the field is present, its color must contribute to the voronoi polygon's color
            val point = points(i)(j) //corresponding point in 2D space
            // assert(point!=None,"we should have defined the color of non existing points")
            if (point.isDefined)
              voronoi(point.get).addColor(color) //updating voronoi's polygon color
          }

    }

  }

  /** when displayed points are modified by either adding or removing locus,
   * recompute the triangles, and then the voronoi hashtable */
  private def voronoise(): Unit = {
    try {
      val triangulator = new DelaunayTriangulator(displayedPoint.toList.asJava)
      val t = time(triangulator.triangulate(), "triangulator.triangulate()")

      triangleSoup = triangulator.getTriangles.asScala.toList
      println(t / triangleSoup.size + "ms par triangle")
    } catch {
      case e: NotEnoughPointsException =>
    }
    voronoi = HashMap() ++ displayedPoint.map((v: Vector2D) => v -> new Voronoi(v))
    for (t <- triangleSoup) {
      t.orientCCW() //triangles are oriented counter clockWise
      //we set the triangles
      for (p <- List(t.a, t.b, t.c))
        voronoi(p).addTriangle(t) //we collect all the triangle incident to each PE
    }
    //  val bbP = toPolygon(boundingBox) //smallest rectangles containing all the points
    for ((_, v) <- voronoi) {
      v.orderTriangles()
      v.setPolygon(boundingBox)
    }
  }

  /**
   * @param l a given locus on the medium.
   * @return all the point coordinate sampling l
   */
  private def pointSet(l: Locus) = {
    var res: Set[Vector2D] = Set()
    for (p <- locusPlane(l))
      res ++= p.flatMap((a: Array[Option[Vector2D]]) => a.toList.flatten).toSet //toList.asJava
    res
  }

  //primitive fields used to construct initial configurations
  private val origin = new Vector2D(0, 0)
  private val center = new Vector2D(nbLineCA / 2, nbColCA / 2)

  /** different possible inits
   * declared with lazy to spare memory, since only one or two will be instanciated
   * make use of primitives fields declared in medium to simplify the programming */
  private lazy val centerInit: InitMold = new InitMold(V(), 1) {
    setBoolVField(center)
  }
  private lazy val debugInit: InitMold = new InitMold(V(), 1) {
    setBoolVField(new Vector2D(3, nbColCA - 1))
  }
  private lazy val yaxisInit: InitMold = new InitMold(V(), 1) {
    for (i <- 0 until nbLineCA) setBoolVField(i, 0)
  }
  private lazy val dottedBorderInit: InitMold = new InitMold(V(), 1) {
    for (i <- 0 until nbLineCA) if (i % 1 == 0) {
      setBoolVField(i, 0)
      setBoolVField(i, nbColCA - 1)
    }
    for (i <- 0 until nbColCA) if (i % 1 == 0) {
      setBoolVField(0, i)
      setBoolVField(nbLineCA - 1, i)
    }
  }

  /** the def fields is generated for each locus, */
  private val defInit: HashMap[Locus, InitMold] = HashMap() ++ List(E(), F(), T(V(), E())).map((l: Locus) =>
    l -> new InitMold(l, 1) {
      for (d <- 0 until l.density)
        for (i <- 0 until nbLineCA)
          for (j <- 0 until nbColCA)
            if (locusPlane(l)(d)(i)(j).isDefined)
              setMemField(d, i, j)
    }
    //we have to iterate on the 6 memFields, and check on line points to see if the neighbor is available.
  )


  /**
   *
   * @param initMethodName indicates which init is to be  applied, based on this medium
   * @return an  "Init" which can initialize a layer
   */
  def initSelect(initMethodName: String, l: Locus): Init = initMethodName match {
    case "center" => centerInit
    case "debug" => debugInit
    case "def" => defInit(l)
    case "yaxis" => yaxisInit
    case "border" => dottedBorderInit
  }


  /**
   * contains material for creating "Init" object which can initialize a layer
   * sub class of medium because for amorphous medium we will need to access the topology of the medium
   *
   * @param locus locus of field being initialized
   * @param nbit  equals to 1 now, could be allowed to become >1 if we make Init for integer layer.
   */
  class InitMold(val locus: Locus, val nbit: Int) extends Init {
    assert(nbit == 1, "we assume that we do not initalize int fields, only boolean fields")
    /** use as a tmp list of arrays of booleans, to more  easily computes the initial values */
    val memFields: Array[Array[Array[Boolean]]] = Array.ofDim[Boolean](locus.density * nbit, nbLineCA, nbColCA)
    /** simplification for the common case which is a boolV field */
    val boolVField: Array[Array[Boolean]] = if (locus == V()) memFields(0) else null

    /**
     * fills the set of memory fields corresponding to a CA field, according to a given init wished for
     *
     * @param CAmemFields memory fields to fill
     */
    override def init(CAmemFields: Array[Array[Int]]): Unit = {
      assert(CAmemFields.length == memFields.length, "the number of fields used in CA memory does not corresponds")
      for ((lCA, lCAmem: Array[Int]) <- memFields zip CAmemFields) { //dot iteration, we iterate on the dot product of the two ranges
        encode(lCA, lCAmem)
        //encodeInterleavRot(nbLineCA, nbColCA, lCA, lCAmem)
        //prepareShift(nbBlock, blockSize, lCAmem)
      }
    }


    def setMemField(d: Int, i: Int, j: Int): Unit = {
      memFields(d)(i)(j) = true
    }

    /**
     *
     * @param p a point within the medium
     * @return set the corresponding value of the boolVfield being initialized
     */
    def setBoolVField(p: Vector2D): Unit = {
      boolVField(round(p.x).toInt)(round(p.y).toInt) = true
    }

    def setBoolVField(i: Int, j: Int): Unit = {
      boolVField(i)(j) = true
    }

  }

}


object Medium {
  /**
   *
   * @param nbColCA   numbrt of columns
   * @param nbLineCA  number of rows.
   * @param widthLt30 width of the pannel in which we draw
   * @return builds the non toroidal hexagonal grid for the CA pannel available, assuming we know the width of the CA pannel
   */
  def apply(nbLineCA: Int, nbColCA: Int, widthLt30: Int): Medium = {
    val width = if (nbColCA < 30) widthLt30 else 2 * widthLt30 //we see that for 64 column we draw the CA in the full available width by using two cells.
    val radiusSqrt = Math.floor(width.toDouble / (2 * nbColCA - 1)) //we compute radius so that the CA fills the available space on the pannel,
    // normally we assume that the number of lines is the number of columns divided by sqrt(2)
    val radius = if (nbLineCA * 1.1 < nbColCA) radiusSqrt else (radiusSqrt * nbColCA) / (nbLineCA * 1.4)
    //the height should be around 1/sqrt2 the width
    assert(radius > 0, "not enough space to draw voronoi")
    //computation of point location in 2D space
    val vertices = createPoints(nbLineCA, nbColCA)
    val deltax = 2 * radius
    val deltay = Math.sqrt(3) * radius
    val bb = (
      ((nbColCA - 1) * deltax + deltax / 2).toInt,
      ((nbLineCA - 1) * deltay).toInt): Dimension
    for (i <- 0 until nbLineCA) {
      val startx = if (i % 2 == 0) 0 else deltax / 2
      for (j <- 0 until nbColCA)
        vertices(i)(j) = Some(new Vector2D(startx + j * deltax, i * deltay))
    }
    //computation of relative neighboring relationship
    val even: Array[(Int, Int)] = Array((0, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0))
    val odd: Array[(Int, Int)] = Array((0, 1), (1, 1), (1, 0), (0, -1), (-1, 0), (-1, 1))
    val neighbors: Array[Array[Array[(Int, Int)]]] = Array.ofDim[(Int, Int)](6, nbLineCA, nbColCA)
    for (i <- 0 until nbLineCA)
      for (j <- 0 until nbColCA)
        for (d <- 0 until 6)
          neighbors(d)(i)(j) = if (i % 2 == 0) even(d) else odd(d)

    //encoding and decoding differs , depending wether the number of columns is bigger than 30 or not
    if (nbColCA >= 30)
      new Medium(nbLineCA, nbColCA, bb, vertices, neighbors) {
        assert(nbColCA % 30 == 0, "nbCol is a multiple of 30")
        /** number of ints needed storing the booleans of one bit plane of the CA memory */
        override val nbInt32: Int = (nbLineCA * nbColCA) / 30
        /** the number of "macro columns, two if nbColumn=60" */
        val nbBlock: Int = nbColCA / 30
        /** we need to insert one integer as a buffer between each macro columns, plus two before and one after */
        override val nbInt32CAmem: Int = (nbLineCA + 1) * nbBlock + 2
        override val propagate4Shift: PrShift = (h: Array[Int]) => {
          val blockSizeInterleaved = nbLineCA + 1
          val nbInt32total: Int = nbBlock * blockSizeInterleaved //we have to take the interleaved space into account
          val nbInnerLoop: Int = nbBlock
          for (i <- 0 until nbInnerLoop)
            for (j <- i * blockSizeInterleaved until (i + 1) * blockSizeInterleaved) {
              UtilBitJava.propagateBit1and30(h, 1 + j, 1 + (j + blockSizeInterleaved) % nbInt32total)
            }
        }

        /**
         * encode from boolean to ints 32 bits
         *
         * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
         * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
         */
        override def encode(memCAbool: Array[Array[Boolean]], memCAint32: Array[Int]): Unit = {
          //symetric case: we need several ints, in order to store one line of the CA
          for (i <- 0 until nbLineCA) { //we process line i whose length is nbColCA
            /** how much do we need to rotate right */
            val shift = (i / 2) % nbColCA
            lineToInts(rotateLeft(memCAbool(i), shift), memCAint32, i * nbBlock, min((i + 1) * nbBlock, nbColCA), nbBlock, nbLineCA) //rotation is done on the whole CA lines.
          }
          interleaveSpace(memCAint32, nbBlock, nbLineCA)
        }

        /**
         * decodes, from Int 32 bits to booleans
         *
         * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
         * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
         */
        override def decode(memCAint32: Array[Int], memCAbool: Array[Array[Boolean]]): Unit = {
          val tmp = copyArray(memCAint32)
          unInterleaveSpace(tmp, nbBlock, nbLineCA)
          for (i <- 0 until nbLineCA) { //we iterate on the CA lines
            intsToLine(tmp, memCAbool(i), i * nbBlock, min((i + 1) * nbBlock, nbInt32), nbBlock, nbLineCA)
            /** how much do we need to rotate right */
            val shift = (i / 2) % nbColCA
            memCAbool(i) = rotateRight(memCAbool(i), shift).toArray //rotation is done on the whole CA lines.
          }
        }
      }
    //one int32 stores one or several sub= line, encoded on 30 of its bits
    else new Medium(nbLineCA, nbColCA, bb, vertices, neighbors) {
      val nbLignePerInt32 = 32 / (nbColCA + 2)
      assert((nbColCA == 6 || nbColCA == 8 || nbColCA == 14) && (nbLineCA % nbLignePerInt32) == 0, "nbCol must be  6, 8 or 14, all the int32 are used completely")
      /** number of ints needed storing the booleans of one bit plane of the CA memory */
      override val nbInt32: Int = nbLineCA / nbLignePerInt32 //for each lines, we need two separating bits
      /** number of Int32 needed for one bit plan of the CA memory **/
      override def nbInt32CAmem: Int = 3 + nbInt32 //we need two extra int32 before and one int32 after.
      override val propagate4Shift: PrShift = new PrShift() {
        def propagate4shift(t: Array[Int]): Unit = {
          val last = t(t.length - 2) //last integer
          val first = t(2) //first integer. normal bits start at t[2]
          t(1) = last >>> (nbColCA + 2) //we start by computing  the very first integer t[1]
          t(t.length - 1) = first << (nbColCA + 2) //and then the very last integer t[t.length - 2]

          val masks: Map[Integer, Integer] = UtilBitJava.mask.asScala.toMap
          val m: Integer = masks(new Integer(nbColCA)).toInt
          for (i <- 1 until t.length)
            t(i) = propagateBitxand1(t(i), nbColCA, m)
          /*for(i <- 1 until t.length)
            if(nbColCA==6)propagateBit6and1(t,i)
            else propagateBit14and1(t,i)
*/


        }
      }
      //PrepareShift.prepareShiftGte30
      /**
       * encode from boolean to ints 32 bits
       *
       * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
       * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
       */
      override def encode(memCAbool: Array[Array[Boolean]], memCAint32: Array[Int]): Unit = {
        for (i <- 0 until nbLineCA) { //we iterate on the CA lines,
          /** how much do we need to rotate */
          val shift = (i / 2) % nbColCA
          val rotated = rotateLeft(memCAbool(i), shift)
          /** index of target Int32, which implements interleaving */
          val index = i % nbInt32
          memCAint32(index) = memCAint32(index) << 1 //separating bit
          memCAint32(index) = push(memCAint32(index), rotated)
          memCAint32(index) = memCAint32(index) << 1 //separating bit
        }
        interleaveSpace(memCAint32, 1, nbInt32) //insert the necessary spaces
      }

      /**
       * decodes, from Int 32 bits to booleans
       *
       * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
       * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
       */
      override def decode(memCAint32: Array[Int], memCAbool: Array[Array[Boolean]]): Unit = {
        val tmp = copyArray(memCAint32)
        unInterleaveSpace(tmp, 1, nbInt32)
        for (i <- (0 until nbLineCA).reverse) {
          val index = i % nbInt32
          tmp(index) = tmp(index) >>> 1 //skipping separating bit
          tmp(index) = pop(tmp(index), memCAbool(i)) //lecture de la iéme ligne
          tmp(index) = tmp(index) >>> 1 //skipping separating bit
          /** how much do we need to rotate right */
          val shift = (i / 2) % nbColCA
          memCAbool(i) = rotateRight(memCAbool(i), shift).toArray
        }
      }
    }

  }

  /** Allocates memory for a 2D array of points */
  private def createPoints(h: Int, w: Int): pointLines = Array.ofDim[Option[Vector2D]](h, w)

  private def copyArray(t: Array[Int]): Array[Int] = {
    val tmp = Array.ofDim[Int](t.length) //we use tmp when decoding in order to to avoid modify the CA memory
    t.copyToArray(tmp)
    tmp
  }


  /** represent the relative offset to get the neighbors in another row and column
   * neigbor can be non existent, in which case it 'll be None */
  type neighbor = Option[(Int, Int)]

  /**
   *
   * @param tuple  first tuple
   * @param tuple1 second tuple
   * @return summ of tuples
   */
  private def add2(tuple: (Int, Int), tuple1: (Int, Int)) = (tuple._1 + tuple1._1, tuple._2 + tuple1._2)

  /**
   *
   * @param ni input to test
   * @param n  maximum allowed
   * @return true if 0<=ni<=n
   */
  private def insideInterval(ni: Int, n: Int) = 0 <= ni && ni < n


}