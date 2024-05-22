package simulator //toto

import compiler.{T, _}
import triangulation.{DelaunayTriangulator, NotEnoughPointsException, Triangle2D, Vector2D, Voroonoi}

import java.util
//import de.alsclo.voronoi.graph.Voronoi
import simulator.CAtype.pointLines
import simulator.UtilBitJava.{moveBitxtoy, propagateBit14and1, propagateBit6and1, propagateBitxand1}
import simulator.{Controller, Env, PrShift, UtilBitJava}
import simulator.Medium._
import triangulation.Utility._

import java.awt.Color
import scala.collection.IterableOnce.iterableOnceExtensionMethods
import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}
import scala.math.{min, random, round}
import scala.swing.Dimension
import scala.swing.Swing.pair2Dimension


/**
 *
 * Provide a partition in 2D space into polygon, for representing the state of the medium
 * locus are distributed in lines, thus having 2 integer coordinates,
 * vertices are displayed from the start
 * together with a neighborood relationship between locus for computing communication during transfers
 *
 * @param env         the associated env, (needed,  to pick the random numbers generator).
 * @param nbCol       max number of points per line
 * @param nbLine      number of lines
 * @param boundingBox Rectangles containing all the points, normally it is also exactly the dimension of the CA pannel.
 * @param vertice     location of the vertices (where the real processing elements are located)
 * @param neighbors encodes the whole architecture of the medium
 * coordinates of the neighbors relative to those of the center
 * For the hexagonal it is the same for all lines with even (resp. odd) index
 *
 */
abstract class Medium(val env: Env, val nbLine: Int, val nbCol: Int, val boundingBox: Dimension,
                      val vertice: pointLines, val neighbors: Array[Array[Array[(Int, Int)]]])
  extends InitSelect {
  /** number of Int32 needed to store  the boolean of one bit plane  * */
  def nbInt32: Int

  /** total  number of Int32 needed for one bit plane, is equal to nbInt32 plus some integers needed for separating bits.   * */
  def nbInt32total: Int

  /** Implements communication needed to propagete bits so that shifting can be implemented with just << or >>
   * and miroring line and columns, so that Gabriel centers will appear on border */
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
   * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
   * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
   * */
  def decode(memCAint32: Array[Int], memCAbool: Array[Array[Boolean]]): Unit

  /**
   *
   * @param ni input x coordinate
   * @param nj input y coordinate
   * @return true if the coordinates indicate a point within the cellular automaton
   */
  private def inside(ni: Int, nj: Int) = insideInterval(ni, nbLine) && insideInterval(nj, nbCol)

  /**
   *
   * @param d neighbor index between 0 and 5 (could be 4 or up to 6 for amorphous)
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
   * */
  private def neigborEdge(d: Int, i: Int, j: Int): Option[Vector2D] = {
    if (d < 3)
      locusPlane(E())(d)(i)(j)
    else {
      val n: (Int, Int) = neigborsAbs(d, i, j)
      val p: Option[Vector2D] = tryFind(n)
      if (p.isDefined) //the edge does exists
        locusPlane(E())(d - 3)(n._1)(n._2)
      else None
    }
  }

  /**
   *
   * @param a angle between 0 and 2
   * @param o orientation between 0 and 1
   * @param i x coordinate
   * @param j y coordinate
   * @return the point representing the neighbor edge, if that edge exists
   *         we distinguish the case o=0 in which case the edge can be accessed directly
   *         from the case o=1 d=3,4,5 in which case we have to first see if neighbor is defined and if so, take it d-3 edge
   * */
  // private def neigborEdgeh0h1d0d1ad0ad1(a:Int,o:Int, i: Int, j: Int) = neigborEdge(a+3*o,i,j)
  private def neigborEdgeh0h1d0d1ad0ad1(a: Int, o: Int, i: Int, j: Int) = neigborEdge(a, i, j)

  /**
   *
   * @param a angle between 0 and 2
   * @param o orientation between 0 and 1
   * @param i x coordinate
   * @param j y coordinate
   * @return the point representing the neighbor vertice, if that vertice exists
   *         we distinguish the case o=0 in which case the vertice can be accessed directly
   *         from the case o=1 d=3,4,5 in which case we compute the indexes and check it lies within the defining bounding box
   * */
  private def neigborVertexh0h1d0d1ad0ad1(a: Int, o: Int, i: Int, j: Int): Option[Vector2D] =
    if (o == 0) vertice(i)(j)
    else {
      val n: (Int, Int) = neigborsAbs(a, i, j)
      val p: Option[Vector2D] = tryFind(n)
      if (p.isDefined) //the vertex does exists
        vertice(n._1)(n._2)
      else None
    }


  /** contains points associated to all locus, locus by locus, each point line is a plane,
   * the number of pointlines for a given locus corresponds to the locus density,
   * the ordedr of point lines for a given locus is standardized and the standard is specified
   * the arangment is such that broadcasting is done by doubling or tripling the value
   * which means that all the T neighbors of a given simplicial site are stacked in sequence */
  var locusPlane: HashMap[Locus, Array[pointLines]] = HashMap()
  locusPlane += V() -> Array(vertice) //adds all vertices , its a singleton array because vertice density is only 1.
  locusPlane += E() -> { //order is h,d,ad
    val res = Array.ofDim[Option[Vector2D]](3, nbLine, nbCol)
    for (dir <- 0 until 3) //we consider half of the neighbors first is east, second is southeast, third is southwest, ...
      for (i <- 0 until nbLine)
        for (j <- 0 until nbCol) {
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
    F() -> { //order is down and then up ( clock and trigo)
      val res = Array.ofDim[Option[Vector2D]](2, nbLine, nbCol) //first is down, second is up
      for (dir <- 0 until 2)
        for (i <- 0 until nbLine)
          for (j <- 0 until nbCol) {
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

  private val weight = 0.666 //transfer locus are not located in the middle
  private val weight2 = 0.9 //transfer locus are not located in the middle
  locusPlane += //todo mettre des lazy
    T(V(), E()) -> { //neighbor are east, southeast, southwest, west,  north west, northeast
      val res = Array.ofDim[Option[Vector2D]](6, nbLine, nbCol)
      for (dir <- 0 until 6)
        for (i <- 0 until nbLine)
          for (j <- 0 until nbCol) {
            val eddge: Option[Vector2D] = neigborEdge(dir, i, j) //the edge we want to consider
            res(dir)(i)(j) =
              if (eddge.isEmpty) None
              else Some(vertice(i)(j).get.mult(weight).add(eddge.get.mult(1 - weight))) //location nearer to the vertice
          }
      res
    }

  locusPlane +=
    T(V(), F()) -> { //neighbor are se,s,sw,nw,n,ne
      def f(d: Int, i: Int, j: Int) = if (inside(i, j)) locusPlane(F())(d)(i)(j) else None

      val res = Array.ofDim[Option[Vector2D]](6, nbLine, nbCol) //first is down, second is up

      for (i <- 0 until nbLine) for (j <- 0 until nbCol) {
        val jup = if (i % 2 == 1) j else j - 1
        val nf: List[Option[Vector2D]] = List(f(0, i, j), f(1, i, j), f(0, i, j - 1),
          f(1, i - 1, jup), f(0, i - 1, jup), f(1, i - 1, jup + 1)) // the six neighborFaceCenters in the order se,s,sw,nw,n,ne
        for (dir <- 0 until 6)
          res(dir)(i)(j) =
            if (nf(dir).isEmpty) None
            else Some(vertice(i)(j).get.mult(weight).add(nf(dir).get.mult(1 - weight))) //location nearer to the vertice
      }
      res
    }
  locusPlane +=
    T(E(), V()) -> {
      val res = Array.ofDim[Option[Vector2D]](6, nbLine, nbCol) //first is down, second is up
      for (dir <- 0 until 6) //order is h0, h1,d0,d1,ad0, ad1
        for (i <- 0 until nbLine)
          for (j <- 0 until nbCol) {
            val angle: Int = dir / 2 //angle can be h,d,ad
            val orientation = dir % 2 //todo check that if orientation is zero, then the vertice owns the edge.
            val edge = neigborEdgeh0h1d0d1ad0ad1(angle, orientation, i, j) //coordinates of the considered  edge
            val vertex = neigborVertexh0h1d0d1ad0ad1(angle, orientation, i, j) //coordinates of the considered vertex
            res(dir)(i)(j) =
              if (edge.isEmpty || vertex.isEmpty) None
              else Some(edge.get.mult(weight).add(vertex.get.mult(1 - weight))) //location is nearer to the edge
          }
      res
    }
  locusPlane += T(E(), F()) -> { //bugici
    val res = Array.ofDim[Option[Vector2D]](6, nbLine, nbCol) //first is down, second is up
    for (i <- 0 until nbLine) for (j <- 0 until nbCol) {
      /** d is 0 pour down, 1 pour up */
      def face(d: Int, i: Int, j: Int) = if (inside(i, j)) locusPlane(F())(d)(i)(j) else None //computes the four faces framing the three edges

      val jup = if (i % 2 == 1) j + 1 else j //ordone premier triangle
      val fourFace = Array(face(1, i - 1, jup), face(0, i, j), face(1, i, j), face(0, i, j - 1))
      for (dir <- 0 until 3) for (or <- 0 until 2) {
        res(2 * dir + or)(i)(j) = if (fourFace(dir + or).isEmpty) None else
          Some(locusPlane(E())(dir)(i)(j).get.mult(weight).add(fourFace(dir + or).get.mult(1 - weight)))
      }
    }
    res

  }

  locusPlane += T(F(), V()) -> {
    def cv(d: Int, i: Int, j: Int) = tryFind(neigborsAbs(d, i, j)).get //coordinate of the neighbor vertice which we know to be defined

    val resFv = Array.ofDim[Option[Vector2D]](6, nbLine, nbCol) //first is down, second is up
    for (i <- 0 until nbLine)
      for (j <- 0 until nbCol) {
        val v = Array.ofDim[Vector2D](3)
        val face = (0 to 1).map(locusPlane(F())(_)(i)(j)) //the two face optionnal location
        if (face(0).isDefined) { //dowface exist we compute its nearby v transfers location dp,db1,db2
          v(0) = cv(1, i, j); //vertice adjacent to dp
          v(1) = cv(0, i, j); //vertice adjacent to db1
          v(2) = vertice(i)(j).get //vertice adjacent to db2
          for (k <- 0 until 3) {
            resFv(k)(i)(j) = Some(face(0).get.mult(weight).add(v(k).mult(1 - weight)))
          }
        }
        else for (k <- 0 until 3) resFv(k)(i)(j) = None
        if (face(1).isDefined) { //upface exist we compute its nearby v transfers location
          v(0) = vertice(i)(j).get //vertice adjacent to up
          v(1) = cv(2, i, j); //vertice adjacent to ub1
          v(2) = cv(1, i, j); //vertice adjacent to ub2
          for (k <- 3 until 6) {
            resFv(k)(i)(j) = Some(face(1).get.mult(weight).add(v(k - 3).mult(1 - weight)))
          }
        }
        else for (k <- 3 until 6) resFv(k)(i)(j) = None
      }
    resFv;
  }
  locusPlane += T(F(), E()) -> {
    def ce(d: Int, i: Int, j: Int) = locusPlane(E())(d)(i)(j).get //coordinate of the edge toward direction d

    val resFe = Array.ofDim[Option[Vector2D]](6, nbLine, nbCol) //first is down, second is up
    for (i <- 0 until nbLine) for (j <- 0 until nbCol) {
      val jdown = if (i % 2 == 1) j else j - 1
      val e = Array.ofDim[Vector2D](6) //the three edge neighbor of a given face.
      val face = (0 to 1).map(locusPlane(F())(_)(i)(j)) //the two face optionnal location
      if (face(0).isDefined) { //dowface exist we compute its nearby e transfers location db,ds1,ds2
        e(0) = ce(0, i, j) //vertice adjacent to dp
        e(1) = ce(2, i, j + 1) //vertice adjacent to db1
        e(2) = ce(1, i, j) //vertice adjacent to db2
        for (k <- 0 until 3)
          resFe(k)(i)(j) = Some(face(0).get.mult(weight).add(e(k).mult(1 - weight)))
      }
      else for (k <- 0 until 3) resFe(k)(i)(j) = None
      if (face(1).isDefined) { //upface exist we compute its nearby v transfers location
        e(3) = ce(0, i + 1, jdown) //vertice adjacent to up
        e(4) = ce(2, i, j); //vertice adjacent to ub1
        e(5) = ce(1, i, j); //vertice adjacent to ub2
        for (k <- 3 until 6)
          resFe(k)(i)(j) = Some(face(1).get.mult(weight).add(e(k).mult(1 - weight)))
      }
      else for (k <- 3 until 6) resFe(k)(i)(j) = None
    }
    resFe
  }
    for (locus <- locusPlane.keys)
      assert(locusPlane(locus).length == locus.density)

  var triangleSoup: List[Triangle2D] = List()
  /** all the voronoi's polygons plus features */
  var voronoi: HashMap[Vector2D, Voroonoi] = HashMap()
  /** points  being displayed (whose voronoi are colored) */
  var displayedPoint: Set[Vector2D] = Set()

  /** computes displayed points */

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



  def resetColorVoronoi(L: Set[Locus]): Unit =
    for (l <- L)
      for (points2D: pointLines <- locusPlane(l))
        for (i <- 0 until nbLine)
          for (j <- 0 until nbCol) {
            val point: Option[Vector2D] = points2D(i)(j) //corresponding point in 2D space
            if (point.isDefined)
              voronoi(point.get).resetColor() //updating voronoi's polygon color
          }

  /** we create that array once and forall to decode memory bit planes */
  private val bitPlaneBuffer = Array.ofDim[Boolean](nbLine, nbCol)
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
      decode(plane, bitPlaneBuffer) //we convert the compact encoding on Int32, into simple booleans
      for (i <- 0 until nbLine)
        for (j <- 0 until nbCol)
          if (bitPlaneBuffer(i)(j)) { //the field is present, its color must contribute to the voronoi polygon's color
            val point = points(i)(j) //corresponding point in 2D space
            // assert(point!=None,"we should have defined the color of non existing points")
            if (point.isDefined)
              voronoi(point.get).addColor(color) //updating voronoi's polygon color
          }

    }

  }

  private def ensureUniqueDisplayedPoint(): Unit = {
    case class caseVector2D(x: Int, y: Int) {}
    val big: Int = 1000000
    val setset: Set[caseVector2D] = HashSet() ++ displayedPoint.map((v: Vector2D) => caseVector2D((v.x * big).toInt, (v.y * big).toInt))
    System.out.println(setset.size + " " + displayedPoint.size)
    assert(setset.size == displayedPoint.size)
  }


  /** when displayed points are modified by either adding or removing locus,
   * recompute the triangles, and then the voronoi hashtable */
  private def voronoise(): Unit = {
    //voronoiseFast() fortune's algo is not so fast.
    //we must check that displayedPoint does not contains duplicate
    ensureUniqueDisplayedPoint()
    try {
      val triangulator = new DelaunayTriangulator(displayedPoint.toList.asJava)
      val t = time(triangulator.triangulate(), "triangulator.triangulate()")

      triangleSoup = triangulator.getTriangles.asScala.toList
      println(t / triangleSoup.size + "ms par triangle")
    } catch {
      case e: NotEnoughPointsException =>
    }
    voronoi = HashMap() ++ displayedPoint.map((v: Vector2D) => v -> new Voroonoi(v))
    for (t <- triangleSoup) {
      t.orientCCW() //triangles are oriented counter clockWise
      //we set the triangles
      for (p <- List(t.a, t.b, t.c))
        voronoi(p).addTriangle(t) //we collect all the triangle incident to each PE p
    }
    //  val bbP = toPolygon(boundingBox) //smallest rectangles containing all the points
    //we want here to draw points in order to debug

    for ((_, v) <- voronoi) {
      v.orderTriangles()
      v.intersectPolygonWithBB(boundingBox)
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


}


object Medium {

  /**
   *
   * @param nbColCA   numbrt of columns
   * @param nbLineCA  number of rows.
   * @param widthLt30 width of the pannel in which we draw
   * @return builds the non toroidal hexagonal grid for the CA pannel available, assuming we know the width of the CA pannel
   */
  def christal(nbLineCA: Int, nbColCA: Int, widthLt30: Int, env: Env): Medium = {
    val width = if (nbColCA < 30) widthLt30 else 2 * widthLt30 //we see that for 64 column we draw the CA in the full available width by using two cells.
    val radiusSqrt = Math.floor(width.toDouble / (2 * nbColCA - 1)) //we compute radius so that the CA fills the available space on the pannel,
    // normally we assume that the number of lines is the number of columns divided by sqrt(2)
    val radius = if (nbLineCA * 1.1 < nbColCA) radiusSqrt else (radiusSqrt * nbColCA) / (nbLineCA * 1.4)
    //the height should be around 1/sqrt2 the width
    assert(radius > 0, "not enough space to draw voronoi")
    //computes lattice location of points  in 2D space
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
    //defini tout, y compris comment on numérote les edge et les faces
    val neighbors: Array[Array[Array[(Int, Int)]]] = Array.ofDim[(Int, Int)](6, nbLineCA, nbColCA)
    for (i <- 0 until nbLineCA)
      for (j <- 0 until nbColCA)
        for (d <- 0 until 6)
          neighbors(d)(i)(j) = if (i % 2 == 0) even(d) else odd(d)
    val neighbors2: Array[Array[Array[(Int, Int)]]] = Array.ofDim[(Int, Int)](6, nbLineCA, nbColCA)
    for (i <- 0 until nbLineCA)
      for (j <- 0 until nbColCA)
        for (d <- 0 until 6)
          neighbors(d)(i)(j) = if (i % 2 == 0) even(d) else odd(d)

    //encoding and decoding differs , depending wether the number of columns is bigger than 30 or not
    if (nbColCA >= 30)
      new Medium(env, nbLineCA, nbColCA, bb, vertices, neighbors) {
        assert(nbCol % 30 == 0, "nbCol is a multiple of 30")
        /** number of ints needed storing the booleans of one bit plane of the CA memory */
        override val nbInt32: Int = (nbLine * nbCol) / 30
        /** the number of "macro columns, two if nbColumn=60, a line is mapped to two columns, in a toroidal way." */
        val nbIntPerLine: Int = nbCol / 30
        val nbLineCAp1 = nbLine + 1 //number of int32 in a column
        /** we need to insert one integer as a buffer between each macro columns, plus two before and one after */
        override val nbInt32total: Int = nbLineCAp1 * nbIntPerLine + 3
        val first = 2; //index of first integer of first line really used
        val last = nbLine + 1 //index of first integer of  last line really used

        override val propagate4Shift: PrShift = new PrShift() {
          def prepareBit(mem: Array[Int]): Unit = propage4Shift(mem)

          def prepareBit(mem: Array[Array[Int]]): Unit = mem.map(propage4Shift(_))

          def propage4Shift(mem: Array[Int]): Unit =
            for (i <- 0 until nbIntPerLine) //i index of a macro columns
              for (j <- i * nbLineCAp1 until (i + 1) * nbLineCAp1) //j traverse macro coloni
                UtilBitJava.propagateBit1and30(mem, 1 + j, 1 + (j + nbLineCAp1) % (nbIntPerLine * nbLineCAp1))

          override def mirror(mem: Array[Int], l: Locus): Unit = if (l.equals(Locus.locusV)) mirrorCopy(mem)

          override def mirror(mem: Array[Array[Int]], l: Locus): Unit = if (l.equals(Locus.locusV)) mem.map(mirrorCopy(_))

          /** do the copying part of mirroring */
          def mirrorCopy(mem: Array[Int]) = {

            def copyLine(src: Int, dest: Int) = copyEntireLine(mem, src + 1, dest + 1, nbIntPerLine, nbLineCAp1)
            def rotateLineRight(i: Int) = rotateEntireLineRigt(mem, i + 1, nbIntPerLine, nbLineCAp1)
            def rotateLineLeft(i: Int) = rotateEntireLineLeft(mem, i + 1, nbIntPerLine, nbLineCAp1)

            //process top line
            copyLine(2, 0)
            rotateLineRight(0) //a rotation of range 1, because the index diff is 2
            //process Bottom line
            copyLine(nbLine - 3, nbLine - 1)
            rotateLineLeft(nbLine - 1) //a rotation of range 1, because the index diff is 2

            //wenow process right and left column
            // we  precomputed  moves movesEven and movesOdd, which differ depending on the parity of the line index
            //we  have to move individual bits, because the moves are not uniform across considered integers
            val movesEven = HashMap[Int, Int](1 -> 0, (nbCol - 3) -> (nbCol - 1)) //here moves are between 0 and nbCOl-1
            val movesOdd = HashMap[Int, Int](2 -> 0, (nbCol - 2) -> (nbCol - 1))
            /** due to rotation, we must add a supplementary shift to even and odd,
             * shifted  moves are still  between 0 and nbCOl-1 */
            def shiftMv(h: Map[Int, Int], shiftRange: Int): Map[Int, Int] = {
              def shift(bitPos: Int, shiftRange: Int): Int = (bitPos + shiftRange + nbCol) % nbCol
              h.map({ case (k, v) => (shift(k, shiftRange), shift(v, shiftRange)) })
            }

            /**
             *
             * @param bitPos position of bit, between 0 and nbColCA
             * @param line   nummer of line within CA
             * @return index of int storing bitPos, and bit possition within this int, between 0 and 31
             */
            def intCoord(bitPos: Int, line: Int) = {
              val numBlock = nbIntPerLine - 1 - bitPos / 30
              val startCol = nbLineCAp1 * numBlock + 2 //first integer in target block
              //+2 because first two int not used
              (startCol + line, bitPos % 30 + 1) //, +1 because first bit is reserved for propagation from neighbor
            }

            /**
             *
             * @param mv   spefies src and target destination for a single bit, within a CA line of nbColCA cells
             * @param line index of line
             */
            def applyMove(mv: (Int, Int), line: Int, mem: Array[Int]) = {
              val (iIntSrc, ibitSrc) = intCoord(mv._1, line)
              val (iIntDest, ibitDest) = intCoord(mv._2, line)
              //for debug printMem(mem(iIntDest))
              val bitRead = getBitx(mem(iIntSrc), ibitSrc)
              mem(iIntDest) = putBitx(mem(iIntDest), ibitDest, bitRead)
              //for debug printMem(mem(iIntDest))
            }

            for (i <- first to last) {
              val moves = shiftMv(if (i % 2 == 0) movesEven else movesOdd, i / 2 - 1) //adds a shift i/2-1 to the move computed for the first line
              //the -1 comes for the fact that we start at 2
              for (mv <- moves) applyMove(mv, (i - 2), mem)
            }
          }
        }
        /**
         * encode from boolean to ints 32 bits
         * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
         * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
         */
        override def encode(memCAbool: Array[Array[Boolean]], memCAint32: Array[Int]): Unit = {
          //symetric case: we need several ints, in order to store one line of the CA
          for (i <- 0 until nbLine) { //we process line i whose length is nbColCA
            /** how much do we need to rotate right */
            val shift = (i / 2) % nbCol
            lineToInts(rotateLeft(memCAbool(i), shift), memCAint32, i * nbIntPerLine, min((i + 1) * nbIntPerLine, nbCol), nbIntPerLine, nbLine) //rotation is done on the whole CA lines.
          }
          interleaveSpace(memCAint32, nbIntPerLine, nbLine)
        }

        /**
         * decodes, from Int 32 bits to booleans
         *
         * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
         * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
         */
        override def decode(memCAint32: Array[Int], memCAbool: Array[Array[Boolean]]): Unit = {
          val tmp = copyArray(memCAint32)
          unInterleaveSpace(tmp, nbIntPerLine, nbLine)
          for (i <- 0 until nbLine) { //we iterate on the CA lines
            intsToLine(tmp, memCAbool(i), i * nbIntPerLine, min((i + 1) * nbIntPerLine, nbInt32), nbIntPerLine, nbLine)
            /** how much do we need to rotate right */
            val shift = (i / 2) % nbCol
            memCAbool(i) = rotateRight(memCAbool(i), shift).toArray //rotation is done on the whole CA lines.
          }
        }
      }
    //one int32 stores one or several sub= line, encoded on 30 of its bits
    else new Medium(env, nbLineCA, nbColCA, bb, vertices, neighbors) {
      val nbLignePerInt32 = 32 / (nbCol + 2)
      assert((nbCol == 6 || nbCol == 8 || nbCol == 14) && (nbLine % nbLignePerInt32) == 0, "nbCol must be  6, 8 or 14, all the int32 are used completely")
      /** number of ints needed storing the booleans of one bit plane of the CA memory */
      override val nbInt32: Int = nbLine / nbLignePerInt32 //for each lines, we need two separating bits
      assert(nbInt32 % 2 == 0) //we need an event number of integers, so that each int will regroupe line with identical parity
      // which will result in a simpler scheme for implementing  the axial symmetry of vertical axis.
      /** number of Int32 needed for one bit plan of the CA memory * */
      override def nbInt32total: Int = 4 + nbInt32 //we need two extra int32 before and two extra int32 after.

      override val propagate4Shift: PrShift = new PrShift() {
        def addMod(i: Int, j: Int) = (i + j + nbCol) % nbCol
        val first = 2;
        val last = 1 + nbInt32
        val maskS: Integer = maskSparse(nbCol)
        val bout = 32 % (nbCol + 2)
        /** we build the move computed for the first line* */
        val (movesEven, movesOdd) = {
          var even: Map[Int, Int] = HashMap.empty
          var odd: Map[Int, Int] = HashMap.empty
          var leftMost = 32 - bout - (nbCol + 2) + 1
          var destLeft = nbCol - 1 //index modulo nbCol of leftmost and right most value of line, place where we will copy
          while (leftMost > 0) //last considered value is 1
          {
            val destRight = addMod(destLeft, -nbCol + 1)
            even = even + (leftMost + addMod(destLeft, -2) -> (leftMost + destLeft))
            odd = odd + (leftMost + addMod(destLeft, -1) -> (leftMost + destLeft))
            even = even + (leftMost + addMod(destRight, +1) -> (leftMost + destRight))
            odd = odd + (leftMost + addMod(destRight, +2) -> (leftMost + destRight))
            leftMost -= nbCol + 2
            destLeft = addMod(destLeft, nbInt32 / 2) //le decalage augmente en rapport avec le nombre d'entier

            if (destLeft >= nbCol)
              throw new Exception("pb addmod")
          }
          (even, odd)
        }


        def prepareBit(mem: Array[Int]): Unit = propagate4Shift(mem)

        def prepareBit(mem: Array[Array[Int]]): Unit = mem.map(propagate4Shift(_))


        def propagate4Shift(mem: Array[Int]): Unit = {
          mem(first - 1) = mem(last) >>> (nbCol + 2) //we start by computing  the very first integer t[first-1]
          mem(last + 1) = mem(first) << (nbCol + 2) //and then the very last integer t[last+1]
          for (i <- 1 until last + 1)
            mem(i) = propagateBitxand1(mem(i), nbCol, maskS)
        }

        override def mirror(mem: Array[Int], l: Locus): Unit = if (l.equals(Locus.locusV)) mirrorCopy(mem)

        override def mirror(mem: Array[Array[Int]], l: Locus): Unit = if (l.equals(Locus.locusV)) mem.map(mirrorCopy(_))

        /** do the copying part of mirroring */
        def mirrorCopy(mem: Array[Int]) = {

          def shift(h: Map[Int, Int], shiftRange: Int): Map[Int, Int] = {
            /** due to rotation, we must add a supplementary shift to the moves even and odd */
            def shift(i: Int, shiftRange: Int): Int = {
              val offset = i - i % (nbCol + 2)
              val iroot = i - offset - 1 //iroot is in the right interval 0..nbCol-1 so as to do a modulo addition
              val ishifted = addMod(iroot, shiftRange)
              val res = ishifted + offset + 1
              if (shiftRange == 0 && res != i) throw new Exception("shift Error")
              res
            }

            h.map({ case (k, v) => (shift(k, shiftRange), shift(v, shiftRange)) })
          }

          /** applies a precomputed list of move, (distinct for even or odd int32. */
          def applyMove(v: Int, moves: Map[Int, Int], mask: Int): Int = {
            var res = v
            for (move <- moves)
              res = moveBitxtoy(res, move._1, move._2, mask)
            res
          }
          //process top line
          val bout = 32 % (nbCol + 2)
          val maskFirst = maskCompact(nbCol) >> bout //cover the first line. we pass over the first two bits, for nbCol+2=10
          val line2 = if (nbInt32 > 2) mem(4) else mem(first) << nbCol + 2 //faut aussi rotationner les bits eux meme
          val line2Trunc = line2 & maskFirst
          val line2rotated = (line2Trunc >>> 1 | (line2Trunc << (nbCol - 1))) & maskFirst
          mem(first) = writeInt32(mem(first), line2rotated, maskFirst) //copy line 2, to line 0
          //process bottom line
          val maskOffset = (nbLignePerInt32 - 1) * (nbCol + 2)
          val maskLast = maskFirst >>> maskOffset
          val linem2 = if (nbInt32 > 2) mem(last - 2) else mem(last) >>> (nbCol + 2)
          val linem2Trunc = linem2 & maskLast //faut aussi rotationner les bits eux meme
          val linem2Rotated = (linem2Trunc << 1 | (linem2Trunc >>> (nbCol - 1))) & maskLast //& 0x00000002
          mem(last) = writeInt32(mem(last), linem2Rotated, maskLast) //copy line last-2, to last line
          //process right and left column using precomputed  moves in movesEven and movesOdd
          val maskSlim = 1 //we will now have to move bit by bit, because the moves are not uniform across a given integers
          for (i <- first - 1 until last + 1) {
            val mv = shift(if (i % 2 == 0) movesEven else movesOdd, i / 2 - 1) //adds a shift i/2-1 to the move computed for the first line
            mem(i) = applyMove(mem(i), mv, maskSlim)
          }
        }
      }
      //PrepareShift.prepareShiftGte30

      /**
       * encode from boolean to ints 32 bits
       *
       * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
       * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
       *                   if nbColCA = 8 memCAint32(k) contains 4  block of 8 bits, the first one starting at position k, with a space of
       *                   nbLine/4 in between
       */
      override def encode(memCAbool: Array[Array[Boolean]], memCAint32: Array[Int]): Unit = {
        for (i <- 0 until nbLine) { //we iterate on the CA lines,
          /** how much do we need to rotate */
          val shift = (i / 2) % nbCol
          val rotated = rotateLeft(memCAbool(i), shift) // takes into account the fact that lines get shifted
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
        for (i <- (0 until nbLine).reverse) {
          val index = i % nbInt32
          tmp(index) = tmp(index) >>> 1 //skipping separating bit
          tmp(index) = pop(tmp(index), memCAbool(i)) //lecture de la iéme ligne
          tmp(index) = tmp(index) >>> 1 //skipping separating bit
          /** how much do we need to rotate right */
          val shift = (i / 2) % nbCol
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



