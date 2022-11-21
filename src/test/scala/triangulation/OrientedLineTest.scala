package triangulation

import org.scalatest.{BeforeAndAfter, FunSuite}
import simulator.CApannel
import triangulation.Vector2D._
import triangulation.OrientedLine._

import scala.swing.Dimension
import scala.swing.{Dimension, Swing}
import scala.swing.Swing.pair2Dimension
import triangulation.Utility._

class OrientedLineTest extends FunSuite with BeforeAndAfter {

  test("intersection") {
    //val (_, s) = DagNode.getGreater(List(n3)); assert(s === Set(n1, n2, n3))
    val v1 = new Vector2D(11, 10)
    val v2 = new Vector2D(2, 13)
    val v3 = new Vector2D(-51, 2)
    /* val v1=new Vector2D(0,0)
     val v2=new Vector2D(0,1)
     val v3=new Vector2D(1,0)*/

    val s1 = segment(v1, v2)
    val s2 = segment(v1, v3)
    assert(s1.contains(v1))
    assert(s1.contains(v2))
    assert(s2.contains(v1))
    assert(s2.contains(v3))
    val newV1 = s1.intersect(s2)
    println(newV1)
    assert(newV1.almostEqual(v1))
  }
  test("selectSide") {
    val square: Dimension = (2, 2): Dimension
    val p = toPolygon(square)
    val center = new Vector2D(1, 1)
    val segments: Seq[OrientedLine] = List(segment(center, new Vector2D(1, 2)),
      segment(center, new Vector2D(2, 1)),
      segment(center, new Vector2D(1, 0)),
      segment(center, new Vector2D(0, 1)))
    for (s <- segments) {
      val (l: Line, side) = s.selectSide(p)
      val newV = s.intersect(l)
      println(newV, side)
    }
    val d = bissector(new Vector2D(-1, 0), new Vector2D(1, 0))
    println(d)

  }

}