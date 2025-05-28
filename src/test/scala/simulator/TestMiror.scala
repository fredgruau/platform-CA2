package simulator

import org.scalatest.{BeforeAndAfter, FunSuite}
import simulator.Medium.christal
import TestEncodeDecode._
import simulator.TestMiror.{isMiror, miror}
import triangulation.Utility._

import scala.util.Random


//
object TestMiror {

  def isMiror(lCA: Array[Array[Boolean]]):Boolean={
    val nbligne= lCA.length; val nbCol=lCA(0).length
    def isMirorUp={ lCA(0).toList==lCA(2).toList}
    def isMirorDown={lCA(nbligne-1).toList==lCA(nbligne-3).toList}
    def isMirorLeft={var i=0;var res=true; for(l<-lCA){res = res && (l(0) == (if(i%2==0) l(2) else l(1)));i+=1  }
    res}
    def isMirorRight={var i=0 ;var res=true;
      for(l<-lCA){res = res &&  (l(nbCol-1)==(if(i%2==0) l(nbCol-2) else l(nbCol-3)));i+=1 }
    res}
    isMirorUp||isMirorDown||isMirorRight||isMirorLeft
  }
  def miror(lCA: Array[Array[Boolean]])={
    val nbligne= lCA.length; val nbCol=lCA(0).length
  def mirorUp={ lCA(0)=lCA(2).clone()}
  def mirorDown={lCA(nbligne-1)=lCA(nbligne-3).clone()}
  def mirorLeft={var i=0; for(l<-lCA){l(0)=if(i%2==0) l(2) else l(1);i+=1  } }
  def mirorRight={var i=0 ; for(l<-lCA){ l(nbCol-1)=if(i%2==0) l(nbCol-2) else l(nbCol-3);i+=1 } }
    mirorUp;mirorDown;mirorRight;mirorLeft
}
}

class TestMiror extends FunSuite with BeforeAndAfter {
  test("mirrorIsMiror") {
    val lCAinput = Array.ofDim[Boolean](12, 14)
    randomFill(lCAinput)
    miror(lCAinput)
    assert(isMiror(lCAinput))
  }
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