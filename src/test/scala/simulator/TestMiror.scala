package simulator

import org.scalatest.{BeforeAndAfter, FunSuite}
import simulator.Medium.christal
import TestEncodeDecode._
import compiler.Locus.locusV
import dataStruc.Util
import dataStruc.Util.{deepCopyArray, isEqualto, isMiror, list, miror, printMat, randomFill}
import triangulation.Utility._

import scala.util.Random



class TestMiror extends FunSuite with BeforeAndAfter {
  test("mirrorIsMiror") {
    val lCAinput = Array.ofDim[Boolean](12, 14)
    randomFill(lCAinput)
    miror(lCAinput)
    assert(isMiror(lCAinput))
  }
  /** takes a random grid of bits, encodes it, miror it, decodes it, checks its been mirored */
  test("smallMiror") {
    val m = christal(12, 14, 30)
    val lCAinput = Array.ofDim[Boolean](12, 14)
    for(i<- 1 to 100) {
      randomFill(lCAinput)
      val lCAoutput = Array.ofDim[Boolean](12, 14)
      val lCAmem = Array.ofDim[Int](10)
      m.encode(lCAinput, lCAmem)
      m.propagate4Shift.mirror(lCAmem)
      m.decode(lCAmem, lCAoutput)
      assert(isMiror(lCAoutput))
    }
  }

  test("smallerMiror") {
    val m = christal(6, 8, 30)
    val lCAinput = Array.ofDim[Boolean](6, 8)
    for(i<- 1 to 100) {
      randomFill(lCAinput)
      val lCAoutput = Array.ofDim[Boolean](6,8)
      val lCAmem = Array.ofDim[Int](6)
      m.encode(lCAinput, lCAmem)
      m.propagate4Shift.mirror(lCAmem)
      m.decode(lCAmem, lCAoutput)
      printMat(lCAoutput)
      assert(isMiror(lCAoutput))
    }
  }


  /** takes a random memory,apply fast miror, check ismirored safe. the propagated bits should not interfere.  */
  test("smallMirorPropagated") {
    val m = christal(12, 14, 30)
    for(i<- 1 to 100) {
      val lCAmem = Array.ofDim[Int](10)
      randomFill( lCAmem)
      m.propagate4Shift.mirror(lCAmem)
      assert(m.isMirorSafe(lCAmem))
    }
  }
  /** check that prepare bits does not modify grid content */
  test("Propagate") {
    val m = christal(12, 14, 30)
    val lCAinput = Array.ofDim[Boolean](12, 14)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](12, 14)
    val lCAmem = Array.ofDim[Int](10)
    m.encode(lCAinput, lCAmem)
    m.propagate4Shift.prepareBit(lCAmem)
    m.decode(lCAmem, lCAoutput)
    assert(isEqualto(lCAoutput,lCAinput))
  }

  /** check that  propagate4shift is idempotent */
  test("smallMirorPropagate2") {
    val m = christal(12, 14, 30)
    val lCAinput = Array.ofDim[Boolean](12, 14)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](12, 14)
    val lCAmem = Array.ofDim[Int](10)

    m.encode(lCAinput, lCAmem)
    m.propagate4Shift.prepareBit(lCAmem)
    val lCAmem2 = lCAmem.clone()
    m.propagate4Shift.prepareBit(lCAmem)
    assert(isEqualto(lCAmem,lCAmem2))
  }



  test("mediumMiror") {
    val m = christal(12, 30, 30)
    val lCAinput = Array.ofDim[Boolean](12, 30)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](12, 30)
    val lCAmem = Array.ofDim[Int](16)
    m.encode(lCAinput, lCAmem)
    m.propagate4Shift.mirror(lCAmem)
    m.decode(lCAmem, lCAoutput)
    assert(isMiror(lCAoutput))
  }

  test("largeMiror") {
    val m = christal(12, 90, 300)
    val lCAinput = Array.ofDim[Boolean](12, 90)

    val lCAoutput = Array.ofDim[Boolean](12, 90)
    val lCAmem = Array.ofDim[Int](48)
    for(i:Int<-0 to 100) {
      randomFill(lCAinput);
      m.encode(lCAinput, lCAmem)
     // randomFill(lCAmem)
      m.propagate4Shift.prepareBit(lCAmem)
      // m.propagate4Shift.mirror(lCAmem)
      m.decode(lCAmem, lCAoutput)
       assert(isEqualto(lCAoutput,lCAinput))

      assert(isMiror(lCAoutput))
    }
  }




  test("smallestMiror") {
    val lCAinput = Array.ofDim[Boolean](6, 8)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](6, 8)
    val lCAmem = Array.ofDim[Int](6)
    val m = Medium.christal(6, 8, 30)
    m.encode(lCAinput, lCAmem)
    m.propagate4Shift.mirror(lCAmem)
    assert(m.isMirorSafe(lCAmem))
    m.decode(lCAmem, lCAoutput)
    assert(isMiror(lCAoutput))
  }
  test("propagateShouldNotChangeDecode") {
    val lCAinput = Array.ofDim[Boolean](6, 8)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](6, 8)
    val lCAoutput2 = Array.ofDim[Boolean](6, 8)
    val lCAmem = Array.ofDim[Int](6)
    val m = Medium.christal(6, 8, 30)
    m.encode(lCAinput, lCAmem)
    m.propagate4Shift.mirror(lCAmem)
    assert(m.isMirorSafe(lCAmem))
    m.decode(lCAmem, lCAoutput)
    assert(isMiror(lCAoutput))
    m.propagate4Shift.prepareBit(lCAmem)
    m.decode(lCAmem, lCAoutput2)
    assert (isEqualto(lCAoutput,lCAoutput2))
    assert(isMiror(lCAoutput2))
  }
}