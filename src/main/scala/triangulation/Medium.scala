package triangulation

import java.awt.Color

import compiler.{E, Locus, V}
import simulator.Simulator.CAtype.pointLines
import triangulation.Medium.createPoints
import triangulation.Utility._

import scala.collection.JavaConverters._
import scala.collection.immutable.HashMap
import scala.swing.Dimension
import scala.swing.Swing.pair2Dimension
import math.round

trait Init {
  /**
   * fills the set of memory fields corresponding to a CA field, according to a given init wished for
   *
   * @param CAmemFields memory fields to fill
   */
  def init(CAmemFields: Array[Array[Int]])
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
 * @param vertice     location of the processing elements
 *
 */
class Medium(val nbLineCA: Int, val nbColCA: Int, val boundingBox: Dimension, val vertice: pointLines) {

  var triangleSoup: List[Triangle2D] = List()
  /** all the voronoi's polygons plus features */
  var voronoi: HashMap[Vector2D, Voronoi] = HashMap()
  private var displayedLocus: Set[Locus] = Set()
  private var displayedPoint: Set[Vector2D] = Set()
  /** contains points associated to all locus, locus by locus  */
  private val locusPlane: HashMap[Locus, Array[pointLines]] = HashMap(
    V() -> Array(vertice), //adds all vertices , its a singleton array because vertice density is only 1.
    E() -> Array(createPoints(nbLineCA, nbColCA), createPoints(nbLineCA, nbColCA), createPoints(nbLineCA, nbColCA)))
  // todo: mettre tout les locus ladedans!
  addNewLocus(V()) //we add the vertices , by default
  /**
   * recompute displayed points and voronoi, upon a increase of displayed points
   *
   * @param l new locus asked for coloring;  there was no other colored field of locus l, and now there is
   */
  def addNewLocus(l: Locus): Unit = {
    if (!displayedLocus.contains(l)) {
      displayedLocus += l
      displayedPoint ++= pointSet(l) //recomputes the displayed point
      val t = time(voronoise(), "voronoise")
    }
  }


  /**
   * recompute displayed points and voronoi, upon a decrease of displayed points
   *
   * @param l locus l is asked for uncoloring, and there is no other colored field of locus l
   */
  def removeLocus(l: Locus): Unit = {
    if (displayedLocus.contains(l)) {
      displayedLocus -= l
      displayedPoint --= pointSet(l) //recomputes the displayed point
      voronoise()
    }
  }

  /** we create that array once and forall to decode memory bit planes */
  private val sandBox = Array.ofDim[Boolean](nbLineCA, nbColCA)

  def resetColorVoronoi() =
    for (l <- displayedLocus)
      for (points2D: pointLines <- locusPlane(l))
        for (i <- 0 until nbLineCA)
          for (j <- 0 until nbColCA) {
            val point = points2D(i)(j) //corresponding point in 2D space
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
  def sumColorVoronoi(locus: Locus, color: Color, bitPlanes: List[Array[Int]]) = {
    assert(bitPlanes.size == locusPlane(locus).size, "the points of the locus must have been generated, and the density must correspond")
    for ((plane, points) <- bitPlanes zip locusPlane(locus)) { //we do a dot iteration simultaneously on pointsPlane, and bitPlane
      decodeInterleavRot(nbLineCA, nbColCA, plane, sandBox) //we convert the compact encoding on Int32, into simple booleans
      for (i <- 0 until nbLineCA)
        for (j <- 0 until nbColCA)
          if (sandBox(i)(j)) { //the field is present, its color must contribute to the voronoi polygon's color
            val point = points(i)(j) //corresponding point in 2D space
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
    val bbP = toPolygon(boundingBox) //smallest rectangles containing all the points
    for ((_, v) <- voronoi) {
      v.orderTriangles()
      v.setPolygon(bbP)
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
  lazy val centerInit: InitMold = new InitMold(V(), 1) {
    setBoolVField(center)
  }

  /**
   *
   * @param initMethodName indicates which init is to be  applied, based on this medium
   * @return an  "Init" which can initialize a layer
   */
  def initSelect(initMethodName: String): Init = initMethodName match {
    case "center" => centerInit
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
    val memFields = Array.ofDim[Boolean](locus.density * nbit, nbLineCA, nbColCA)
    /** simplification for the common case which is a boolV field */
    val boolVField = if (locus == V()) memFields(0) else null

    /**
     * fills the set of memory fields corresponding to a CA field, according to a given init wished for
     *
     * @param CAmemFields memory fields to fill
     */
    override def init(CAmemFields: Array[Array[Int]]): Unit = {
      assert(CAmemFields.size == memFields.size, "the number of fields used in CA memory does not corresponds")
      for ((lCA, lCAmem) <- memFields zip CAmemFields) //dot iteration, we iterate on the dot product of the two ranges
        encodeInterleavRot(nbLineCA, nbColCA, lCA, lCAmem)
    }

    /**
     *
     * @param p a point within the medium
     * @return set the corresponding value of the boolVfield being initialized
     */
    def setBoolVField(p: Vector2D) = {
      boolVField(round(p.x).toInt)(round(p.y).toInt) = true
    }
  }

}


object Medium {
  /**
   *
   * @param nbCol numbrt of columns
   * @param nbRow number of rows.
   * @param width width of the pannel in which we draw
   * @return builds the non toroidal hexagonal grid, assuming we know the width of the CA pannel
   */
  def apply(nbRow: Int, nbCol: Int, width: Int): Medium = {
    val radius = Math.floor(width.toDouble / (2 * nbCol - 1)) //we compute radius so that the CA fills the available space on the pannel
    assert(radius > 0, "not enough space to draw voronoi")
    val vertices = createPoints(nbRow, nbCol)
    val deltax = 2 * radius;
    val deltay = Math.sqrt(3) * radius
    val bb = (
      ((nbCol - 1) * deltax + deltax / 2).toInt,
      ((nbRow - 1) * deltay).toInt): Dimension
    for (i <- 0 until nbRow) {
      val startx = if (i % 2 == 0) 0 else deltax / 2
      for (j <- 0 until nbCol)
        vertices(i)(j) = Some(new Vector2D(startx + j * deltax, i * deltay))
    }
    new Medium(nbRow, nbCol, bb, vertices)

  }

  /** Allocates memory for a 2D array of points */
  private def createPoints(h: Int, w: Int): pointLines = Array.ofDim[Option[Vector2D]](h, w)


  /** represent the relative offset to get the neighbors in another row and column
   * neigbor can be non existent, in which case it 'll be None */
  type neighbor = Option[(Int, Int)]


}