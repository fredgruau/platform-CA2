package simulator

import org.scalatest.{BeforeAndAfter, FunSuite}
import simulator.Medium.christal
import TestEncodeDecode._
import compiler.Locus.locusV
import dataStruc.Util
import dataStruc.Util.{isEqualto, isMiror, isTorus, list, miror, randomFill, torusify}
import triangulation.Utility._

import scala.util.Random





class TestTorusify  extends FunSuite with BeforeAndAfter {
  test("torusIsTorus") {
    {
      val lCAinput = Array.ofDim[Boolean](12, 14)
      randomFill(lCAinput)
      torusify(lCAinput)
      assert(isTorus(lCAinput))
    }
  }
  test("largeTorus") {
    val m = christal(12, 90, 300)
    val lCAinput = Array.ofDim[Boolean](12, 90)

    val lCAoutput = Array.ofDim[Boolean](12, 90)
    val lCAmem = Array.ofDim[Int](48)
    for(i:Int<-0 to 100) {
      randomFill(lCAinput);
      m.encode(lCAinput, lCAmem)
      // randomFill(lCAmem)
      //m.propagate4Shift.prepareBit(lCAmem)
      m.propagate4Shift.torusify(lCAmem)
      m.decode(lCAmem, lCAoutput)
      // assert(isEqualto(lCAoutput,lCAinput))
      assert(isTorus(lCAoutput))
    }
  }

  def printMem(lCA:Array[Array[Boolean]]) =  {
    println(lCA(1).toList)  //coincide juste sur les 6 dernier
    println(lCA(lCA.length-1).toList)
    println("rr")
    println(lCA(0).toList)
    println(lCA(lCA.length-2).toList)
    for(l<-lCA)
      println(l(0)+"  "+l(l.length-1))


    //for (l<-lCA)  println(l.toList)
  }

  test("smallestTorus") {

    val lCAinput = Array.ofDim[Boolean](6, 8)
    randomFill(lCAinput)
    val lCAoutput: Array[Array[Boolean]] = Array.ofDim[Boolean](6, 8)
    val lCAmem = Array.ofDim[Int](6)
    val m = Medium.christal(6, 8, 30)
    m.encode(lCAinput, lCAmem)
    m.propagate4Shift.torusify(lCAmem)
    m.decode(lCAmem, lCAoutput)
    printMem(lCAoutput)
    assert(isTorus(lCAoutput))
  }

  test("smallTorus") {
    val m = christal(12, 14, 30)
    val lCAinput = Array.ofDim[Boolean](12, 14)
    randomFill(lCAinput)
    val lCAoutput = Array.ofDim[Boolean](12, 14)
    val lCAmem = Array.ofDim[Int](10)
    m.encode(lCAinput, lCAmem)
    m.propagate4Shift.torusify(lCAmem)
    m.decode(lCAmem, lCAoutput)
    assert(isTorus(lCAoutput))
  }
 }
