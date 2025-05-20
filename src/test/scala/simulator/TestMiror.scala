package simulator

import org.scalatest.{BeforeAndAfter, FunSuite}
import simulator.Medium.christal
import TestEncodeDecode._
import triangulation.Utility._

import scala.util.Random


//
class TestMiror extends FunSuite with BeforeAndAfter {
  test("smallestMiror") {
    val m= christal(12, 14, 30)
    val lCAinput = Array.ofDim[Boolean](12, 14)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](12, 14)
    val lCAmem = Array.ofDim[Int](9)
    m.encode(lCAinput, lCAmem)

    m.decode(lCAmem, lCAoutput)
    assert(list(lCAinput) == list(lCAoutput))
  }
}