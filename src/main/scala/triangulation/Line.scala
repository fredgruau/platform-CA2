package triangulation

import triangulation.Utility._

/**
 * parameters a,b,c represent the classic eqaution ax+by+c = 0
 *
 * @param a ax
 * @param b +by
 * @param c +c=0
 */
class Line(private val a: Double, private val b: Double, private val c: Double) {
  /** perpendicular direction */
  val normal = new Vector2D(a, b)

  /**
   *
   * @param l line to intersect
   * @return point at the intersection of non parallel lines
   *         given by their equation
   */
  def intersect(l: Line): Vector2D = {
    val det = normal.sinus(l.normal)
    assert(!neglectable(det), "because the lines are not parallel delta should  not be null")
    val newx = b * l.c - l.b * c
    val newy = l.a * c - a * l.c
    // new Vector2D(l.a*c- a*l.c,l.b*c-b*l.c).mult(1/det)
    new Vector2D(newx, newy).mult(1 / det)
  }

  def contains(v: Vector2D): Boolean = neglectable(a * v.x + b * v.y + c)
}

object Line {
  /**
   * Builds a line using two points
   *
   * @param p point on the line
   * @param q other point on the line
   * @return coef a b c of the equation of the line going through those two points.
   */
  def apply(p: Vector2D, q: Vector2D): Line = {
    val a = q.y - p.y
    val b = p.x - q.x
    val c = -1 * (a * q.x + b * q.y)
    new Line(a, b, c)
  }


}
