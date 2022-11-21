package simulator

import org.scalatest.{BeforeAndAfter, FunSuite}
import triangulation.Utility._

import scala.util.Random

class TestEncodeDecode extends FunSuite with BeforeAndAfter {
  /** push and pop a single boolean into an int representing a stack */
  test("push1pop1") {
    val input = 141 //not to big int
    val (newInput, b) = pop(push(input, true))
    assert(b == true)
    assert(newInput == input)
  }


  test("rorrol") {
    val r: Random.type = scala.util.Random
    for (i <- 0 until 10000) {
      val input = r.nextInt() >>> 2
      val shift = r.nextInt() % 30
      val output = ror(input, shift, 30)
      assert(rol(output, shift, 30) == input)
    }

    val input = 141 //not to big int
    val (newInput, b) = pop(push(input, true))
    assert(b == true)
    assert(newInput == input)
  }


  /** codes, and then decodes an array of five booleans into an int */
  test("pushnpopn") {
    val input = Array.ofDim[Boolean](32)
    randomFill(input)
    val output = Array.ofDim[Boolean](32)
    val intCode = push(0, input)
    val popped = pop(intCode, output)
    assert(input.toList == output.toList)
  }

  /** arrays cannot be directly compared for equality, because their adress will
   * be compared. That is why we need to turn them into lists */
  def list[A](input: Array[Array[A]]) =
    input.map(_.toList).toList

  def randomFill(lCAinput: Array[Boolean]): Unit = {
    val r: Random.type = scala.util.Random
    for (i <- 0 until lCAinput.size)
      lCAinput(i) = r.nextBoolean()
  }

  def randomFill(lCAinput: Array[Array[Boolean]]): Unit = {
    val r: Random.type = scala.util.Random
    for (l <- lCAinput)
      randomFill(l)
  }

  test("encodeDecodeInterleavedRorate<=32") {
    val lCAinput = Array.ofDim[Boolean](10, 15)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](10, 15)
    val lCAmem = Array.ofDim[Int](5)
    encodeInterleavRot(10, 15, lCAinput, lCAmem)
    decodeInterleavRot(10, 15, lCAmem, lCAoutput)
    assert(list(lCAinput) == list(lCAoutput))
  }

  /** a different algorithm is used, when the number of column is > 32 */
  test("encodeDecodeInterleavedRorate>32") {
    val lCAinput = Array.ofDim[Boolean](10, 60)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](10, 60)
    val lCAmem = Array.ofDim[Int](20)
    encodeInterleavRot(10, 60, lCAinput, lCAmem)
    decodeInterleavRot(10, 60, lCAmem, lCAoutput)
    assert(list(lCAoutput) == list(lCAinput))
  }
}