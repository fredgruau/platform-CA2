package simulator

import org.scalatest.{BeforeAndAfter, FunSuite}
import triangulation.Medium
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


  test("InterleaveSpace") {
    val a = Array(1, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0)
    val b = Array(1, 2, 3, 4, 5, 6, 7, 8)
    interleaveSpace(a, 2, 4)
    print(a.toList)
    unInterleaveSpace(a, 2, 4)
    assert(a.toList.dropRight(3) == b.toList)
  }
  test("encodeDecode<=32") {
    val lCAinput = Array.ofDim[Boolean](12, 14)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](12, 14)
    val lCAmem = Array.ofDim[Int](9)
    val m = Medium(12, 14, 30)
    m.encode(lCAinput, lCAmem)
    m.decode(lCAmem, lCAoutput)
    assert(list(lCAinput) == list(lCAoutput))
  }

  test("encodeDecodeSingleInt") {
    val lCAinput = Array.ofDim[Boolean](4, 6)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](4, 6)
    val lCAmem = Array.ofDim[Int](4)
    val m = Medium(4, 6, 30)
    m.encode(lCAinput, lCAmem)
    m.decode(lCAmem, lCAoutput)
    assert(list(lCAinput) == list(lCAoutput))
  }

  test("encodeDecodetwoInt") {
    val lCAinput = Array.ofDim[Boolean](6, 8)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](6, 8)
    val lCAmem = Array.ofDim[Int](5)
    val m = Medium(6, 8, 30)
    m.encode(lCAinput, lCAmem)
    m.decode(lCAmem, lCAoutput)
    assert(list(lCAinput) == list(lCAoutput))
  }

  /** a different algorithm is used, when the number of column is > 32 */
  test("encodeDecodeInterleavedRorate>32") {
    val lCAinput = Array.ofDim[Boolean](10, 60)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](10, 60)
    val lCAmem = Array.ofDim[Int](23)
    encodeInterleavRot(10, 60, lCAinput, lCAmem)
    decodeInterleavRot(10, 60, lCAmem, lCAoutput)
    assert(list(lCAoutput) == list(lCAinput))
  }


  test("exchangeOand31") {
    val input = -4 >>> 1 //01111111111111111111111111111110
    val T = Array(input)
    UtilBitJava.propagateBit1and30(T, 0, 0)
    assert(T(0) == -1)
    val T2 = Array(input, input)
    UtilBitJava.propagateBit1and30(T2, 0, 1)
    assert(T2(0) == -1 >>> 1) //01111111111111111111111111111111
    assert(T2(1) == -2) //11111111111111111111111111111110
  }

  test("interleave") {
    for (i <- 0 to 11) {
      val i2 = interleaved(i, 2, 6)
      assert(interleaved(i2, 6, 2) == i)
    }
  }

}