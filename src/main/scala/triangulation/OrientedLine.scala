package triangulation

import java.awt.Polygon

import triangulation.Utility._

/**
 * oriented line is a line plus  an origin and a direction
 *
 * @param vectDir vecteur directeur
 * @param origin  origin
 */
class OrientedLine(private val vectDir: Vector2D, private val origin: Vector2D)
  extends Line(-1 * vectDir.y, vectDir.x, -1 * vectDir.rotpisur2().dot(origin)) {
  override def toString: String = "" + vectDir + "  " + origin

  /**
   *
   * @param l2 another oriented line
   * @return has the same sign as  the sinus of the angle with l2,
   */
  def sinus(l2: OrientedLine): Double = vectDir.sinus(l2.vectDir)

  /**
   *
   * @param p polygon, p either contains, or is adjacent to the origin of this.
   * @return side of the polygon instersected by this.
   * @return line of the plygon which is crossed. and also its index.
   */
  def selectSide(p: Polygon): (Line, Int) = {
    /* if(!p.contains(new Point(origin.x.toInt, origin.y.toInt)))
       println("inside n'est pas inside")*/
    //the point can also be exactly on the border
    val points: List[Vector2D] = fromPolygon(p)
    val sinuses = points.map((v: Vector2D) => sinus(new OrientedLine(v.sub(origin), origin)))
    val lselected = (0 until points.size).filter( //the  points on the perimeter have a positive sinus, until selected
      (i: Int) => (sinuses(i) >= 0) && (sinuses((i + 1) % points.size) <= 0) //after selected it becomes negative
    )
    assert(lselected.size == 1, "there must be a unique crossed side")
    val selected = lselected.head
    (Line(points(selected), points((selected + 1) % points.size)), selected)
  }
}

object OrientedLine {
  /**
   *
   * @param a origin of the oriented line
   * @param b ab is the direction nof the line
   * @return an oriented line with or
   */
  def segment(a: Vector2D, b: Vector2D) = new OrientedLine(b.sub(a), a)

  /**
   *
   * @param a first extremity of a segment [ab]
   * @param b last extremity of a segment [ab]
   * @return he bisector of segment [ab]  as a line orinted 90 degrees with respect to [ab]
   */
  def bissector(a: Vector2D, b: Vector2D) = new OrientedLine(b.sub(a).rotpisur2, a.middle(b))
}
