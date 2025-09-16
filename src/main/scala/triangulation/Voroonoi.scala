package triangulation

import java.awt.{Color, Polygon}

import OrientedLine._
import Voroonoi._
import triangulation.Utility._

import scala.collection.{Set, immutable}
import scala.collection.immutable.Set
import scala.swing.Dimension

/** contains the code for computing the voronoi Cell, as a polygon,
 *
 * @param center points in the center of the cell.
 */
class Voroonoi(val center: Vector2D) {
  var trianglesOK=true
  def addColor(c: Color) = color = Utility.addColor(color, c)
  var color: Color = Color.black;
  /** text to be displayed */
  var text:String = null
  def addText(letter:String)={text=if(text==null) letter else text+letter}
  var int32Code:Int=0
  def addBit(bit:Boolean)={
    val newbit=if(bit) 1 else 0
      int32Code=int32Code<<1 | newbit} //multiplie par 2 et ajoute le nouveau bit.
  def textifyBits(ls:List[String])=
   {
     if(ls.nonEmpty)  for(s<-ls) {
      if ((int32Code & 1) == 1) addText(s)
        int32Code=int32Code>>>1
    }
     else {
       val codeInt:String =""+int32Code
       addText(codeInt)
       int32Code=0
     }
     if(int32Code !=0)
     print(22)
   assert(int32Code==0) //on devrait avoir utilisé tout les bits.
   }
  /** remet a zero pour pouvoir ensuite accumuler */
  def resetColorText() = {color = Color.black; text=null; int32Code=0}


  var discontinuousTriangle = false
  /** list of triangles incident to the center of the voronoi.
   * Its a var, because it is computed later by visiting the triangle's summits*/
  var triangles: List[Triangle2D] = List()
  def addTriangle(t: Triangle2D) =
    triangles ::= t

  /**
   * permutes the summits a,b and c of the triangle until a is the center of the voronoi
   *
   * @param t
   */
  def permute2(t: Triangle2D) = {
    var count = 0
    while (!t.a.isEqual(center) ) {
      count += 1
      if (count > 1000)
        throw new Exception("ca boucle dans permute")
      t.permute()
    }
  }

  /** put the triangles in trigonometric wise order, starting after the border until the border */
  def orderTriangles() = {
    if (triangles.isEmpty) {
      System.out.print("y en a pas des triangles!")
      trianglesOK=false
    }
    else{

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
      val (t1s, t2s) = triangleLeft.partition(_.c.isEqual2( first.b))
      triangleLeft = t2s;
      withCommonSideBefore = t1s
      if (withCommonSideBefore.nonEmpty) { //we found the triangle before, and insert it.
        first = withCommonSideBefore.head
        res = first :: res
      }
    } while (withCommonSideBefore.nonEmpty)
    if (triangleLeft.nonEmpty) //first has no triangle neighbor before, we must be on the outerborder
      do {
        count += 1
        if (count > 1000)
          throw new Exception("ca boucle dans ordertriangle")
        val (lt1, t2s) = triangleLeft.partition(_.b.isEqual2( last.c)) //we look for the triangles on the other end. we know there should be exactly one element matching
        //val (lt1, t2s) = triangleLeft.partition( (t: Triangle2D)=>quasiEqual2(t.b ,last.c) )//we know there should be exactly one element matching
      if (lt1.isEmpty) {
        System.out.print("problem Order triangle, the triangles do not form a segment, they cannot be put in continuity")
        trianglesOK=false  //triangleOK is true if no triangle
      } else
      {val newLast = lt1.head
      res2 = newLast :: res2;
      triangleLeft = t2s;
      last = newLast}
    } while (triangleLeft.nonEmpty && trianglesOK)
    if (!first.b.isEqual(last.c) )//the triangles around the voronoi's center do not form a ring,
      discontinuousTriangle = true // the center of the polygon is onconvex hull of all the point
    triangles = res ::: res2.reverse

    }
  }

  val epsilon = 0.000000000000000001
  import scala.collection.immutable.Set

  /** If voronoi intersect a side of the bounding box, sides stores  the index or the corresponding side.
   * There can be two such indexes, if polygon contains a  corner */
  var sides: Set[Int] = Set()
  def isBorder:Boolean=sides.nonEmpty
  /** will contain the resulting polygon */
  var polygon = new Polygon()

  /** @return if there is a corner, returns its index */
  def corner: Option[Int] = {
    if (sides.size < 2) None
    else {
      val firstSide = sides.reduce(Math.max)
      Some(if (firstSide == 3 && sides.contains(0)) 0 else firstSide) //express a toroidal metric not immediate to grasp
    }
  }

  /**
   * adjust  the polygon' sequence of segments if  it cuts the bounding box.
   * truncate the polygon so that it fits the bounding box
   * by adding points intersectng the bbox, and supressing points outside the bbox
   *
   * @param bb bounding box
   *           Uses the delaunays triangle to determine whether voronoi intersects the bbox
   */
  def intersectPolygonWithBB(bb: Dimension) = {
    val bbP = toPolygon(bb)
    /**
     *
     * @param p polygon
     * @param i index of a point defining the polygon's border
     * @return the point of index i
     */
    def summit(p: Polygon, i: Int) = new Vector2D(p.xpoints(i), p.ypoints(i))

    def cornerPoint: Option[Vector2D] = corner.map((f: Int) => summit(bbP, f))

    /** @param u points on polygon
     * @param v  points on polygon comming after u, in trigonometric order
     * @return intersection  between the bisectrice of [u,v] (here order matters) and the bounding box */
    def pointOnBB(u: Vector2D, v: Vector2D): Vector2D = {
      val bissec = bissector(u, v)
      val (l, side: Int) = bissec.selectSide(bbP)
      sides += side //we need to remember which sides we are a border of.
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
    def truncatedPoly(first: Triangle2D, others: List[Triangle2D], last: Triangle2D): List[Vector2D] = {
      val h1 =hitTheWall(first, true)
      val h2= hitTheWall(last, false)
/*    tentative d'identifier les "creux"
  val crossBeforeBB=h1.nonEmpty && h2.nonEmpty &&
        (h1(0).sub(h2(0)).dot(first.c.sub(last.b))<0)
      if (crossBeforeBB) {
        val l1=bissector(first.c, first.a).asInstanceOf[Line]
        val l2=bissector(last.a,last.b).asInstanceOf[Line]
          val meet=l1.intersect(l2)
           last.computeCenter()::meet:: first.computeCenter() ::others.map(_.computeCenter())
          //System.out.println("rrrere")
      }
      else*/
        hitTheWall(first, true) ::: others.map(_.computeCenter()) ::: hitTheWall(last, false) ::: (cornerPoint.toList)
    }

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

object Voroonoi {
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
