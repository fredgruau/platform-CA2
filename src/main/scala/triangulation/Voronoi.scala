package triangulation

import java.awt.{Color, Polygon}

import OrientedLine._
import Voronoi._
import triangulation.Utility._

import scala.collection.{Set, immutable}
import scala.collection.immutable.Set
import scala.swing.Dimension

/** contains the code for computing the voronoi Cell, as a polygon */
class Voronoi(val center: Vector2D) {


  def addColor(c: Color) = color = Utility.addColor(color, c)


  var color: Color = Color.black;

  def resetColor() = color = Color.black;


  var discontinuousTriangle = false
  var triangles: List[Triangle2D] = List()

  def addTriangle(t: Triangle2D) =
    triangles ::= t

  def permute2(t: Triangle2D) = {
    var count = 0
    while (t.a != center) {
      count += 1
      if (count > 1000)
        throw new Exception("ca boucle dans permute")
      t.permute()
    }
  }

  /** put the triangles in trigonometric wise , starting after the border until the border */

  def orderTriangles() = {
    triangles.map(permute2(_)) //this permutation should be called again, because it will be undone by neighbors also ordering.
    var first = triangles.head //there is allways at least one triangle
    var res: List[Triangle2D] = List(first)
    var res2: List[Triangle2D] = List()
    var withCommonSideBefore: List[Triangle2D] = List()
    var triangleLeft = triangles.tail
    var last: Triangle2D = first
    var count = 0
    do {
      count += 1
      if (count > 1000)
        throw new Exception("ca boucle dans ordertriangle")
      val (t1s, t2s) = triangleLeft.partition(_.c == first.b)
      triangleLeft = t2s;
      withCommonSideBefore = t1s
      if (withCommonSideBefore.nonEmpty) {
        first = withCommonSideBefore.head
        res = first :: res
      }
    } while (withCommonSideBefore.nonEmpty)
    if (triangleLeft.nonEmpty) //first has no triangle neighbor before, we must be on the points convex hull
      do {
        count += 1
        if (count > 1000)
          throw new Exception("ca boucle dans ordertriangle")
      val (lt1, t2s) = triangleLeft.partition(_.b == last.c) //we know there should be exactly one element matching
      // val (lt1, t2s) = triangleLeft.partition( (t: Triangle2D)=>quasiEqual2(t.b ,last.c) )//we know there should be exactly one element matching
      if (lt1.size != 1)
        System.out.print("problem Order triangle")
      val newLast = lt1.head
      res2 = newLast :: res2;
      triangleLeft = t2s;
      last = newLast
    } while (triangleLeft.nonEmpty)
    if (first.b != last.c) //the triangles around the voronoi's center do not form a ring,
      discontinuousTriangle = true // the center of the polygon is onconvex hull of all the point
    triangles = res ::: res2.reverse

  }

  val epsilon = 0.000000000000000001
  import scala.collection.immutable.Set
  /** records one or two sides if corner */
  var sides: Set[Int] = Set()
  var polygon = new Polygon()

  def corner: Option[Int] =
    if (sides.size < 2) None
    else {
      val firstSide = sides.reduce(Math.max)
      Some(if (firstSide == 3 && sides.contains(0)) 0 else firstSide) //express a toroidal metric not immediate to grasp
    }

  /**
   * sets the polygons, take into account if it cuts the bounding box.
   * @param bb bounding box
   */
  def setPolygon(bb: Dimension) = {
    val bbP = toPolygon(bb)
    def cornerPoint: List[Vector2D] = {
      val c = corner
      if (c == None) List()
      else List(new Vector2D(bbP.xpoints(c.get), bbP.ypoints(c.get)))
    }
    /** computes intersection  between the bisectrice of [u,v] and the bounding box */
    def pointOnBB(u: Vector2D, v: Vector2D): Vector2D = {
      val bissec = bissector(u, v)
      val (l, side) = bissec.selectSide(bbP)
      sides += side //we stores which sides we are a border of.
      bissec.intersect(l)
    }
    /**
     *
     * @param t     first or last triangle of a list
     * @param first true if first
     * @return a list of one or two vertices allowing to finish the polygon associated to a PE
     */
    def hitTheWall(t: Triangle2D, first: Boolean): List[Vector2D] =
      if (outside(t))
        if (first) List(pointOnBB(t.c, t.a))
        else List(pointOnBB(t.a, t.b))
      else //if the triangles center is inside the bounding box, we must add it to the polygon.
      if (first) List(pointOnBB(t.b, t.a), t.computeCenter())
      else List(t.computeCenter(), pointOnBB(t.a, t.c))
    /**
     *
     * @param first first triangle when discontinuous, either because there lacks triangle
     *              or because one has its center ouside the bb and is counter for no triangle
     * @param others
     * @param last  last triangle
     * @return
     *
     */
    def truncatedPoly(first: Triangle2D, others: List[Triangle2D], last: Triangle2D): List[Vector2D] =
      hitTheWall(first, true) ::: others.map(_.computeCenter()) ::: hitTheWall(last, false) ::: cornerPoint

    /** true if the center of triangle lies ouside of the bounding box */
    def outside(t: Triangle2D): Boolean = {
      val c = t.computeCenter();
      val epsilon = 0.00000001
      c.x < epsilon || c.x > bb.width - epsilon || c.y < epsilon || c.y > bb.height - epsilon

      //!bbP.inside(t.center.x.toInt, t.center.y.toInt)
    }
    def inside(t: Triangle2D): Boolean = !outside(t)

    polygon.reset()
    triangles.map(permute2(_)) //not necessary but we leave it
    val l: List[Vector2D] =
      if (discontinuousTriangle) { //triangles are missing
        val (insideTriangles, outsideTriangles) = triangles.partition(inside(_))
        val others = if (insideTriangles.size > 1) insideTriangles.reverse.tail.reverse.tail else List.empty[Triangle2D]
        if (insideTriangles.size > 0)
          truncatedPoly(insideTriangles.head, others, insideTriangles.last)
        else //all the triangles are outside!!!
          truncatedPoly(outsideTriangles.head, others, outsideTriangles.last)
      }
      else {
        //we select the adjacent delaunay triangle whose circumCenter falls outside the bounding box.

        val indexTruncated: Int = triangles.indexWhere(outside(_))
        val indexTruncated2: Int = triangles.indexWhere(inside(_))
        if (indexTruncated == -1 || indexTruncated2 == -1) //all inside or all outside
          triangles.map(_.computeCenter()) //on recalcule plusieurs fois le centre
        else { //one of the triangle has its center outside and another has its center inside


          val lastIndexTruncated: Int = triangles.lastIndexWhere(outside(_))
          val insid = triangles.map(inside(_))
          //assert(indexTruncated == lastIndexTruncated, "we make the hypothese that here should be at most one circumcenter outside the bounding box")
          var count = 0
          do {
            (triangles = rotate(triangles, 1))
            count += 1
            if (count > 1000)
              throw new Exception("loops in set polygon")
          }
          while (outside(triangles.head) || inside(triangles.last)) //at the end, the list of triangles is in two pieces.
          val (in, out) = triangles.partition(inside(_))
          val firstOut = out.last
          val lastOut = out.head
          truncatedPoly(firstOut, in, lastOut)
        }
      }
    polygon = toPolygon(l)
  }
}

object Voronoi {
  /**
   *
   * @param l list
   * @param n index of one element
   * @tparam A type of the elements
   * @return the list after n+1 shifts towards the left., element with index n will become first
   */
  def rotate[A](l: List[A], n: Int) = {
    var res: List[A] = l
    var heads: List[A] = List()
    for (i <- 0 to n - 1) {
      heads ::= res.head
      res = res.tail
    }
    res ::: heads.reverse
  }

}
