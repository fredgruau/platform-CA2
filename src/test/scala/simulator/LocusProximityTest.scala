package simulator

import compiler.Locus
import compiler.Locus.{all2DLocus, allLocus, locusV}
import org.scalatest.{BeforeAndAfter, FunSuite}
import simulator.Medium.christal

import scala.collection.immutable
import scala.collection.immutable.HashSet
class LocusProximityTest extends FunSuite with BeforeAndAfter {
  def powerSet[A](xs: Seq[A]): Seq[Seq[A]] =
    xs.foldLeft(Seq(Seq[A]())) {(sets, set) => sets ++ sets.map(_ :+ set)}


  val medium= christal(6, 8, 200)
  val displayedLocus=allLocus.toSet
  var hasBigFaces:immutable.HashSet[Seq[Locus]]=HashSet()
  var hasCrossedFace:immutable.HashSet[Seq[Locus]]=HashSet()
  var hasTrou:immutable.HashSet[Seq[Locus]]=HashSet()
  for(displayedLocus<-powerSet( all2DLocus)){
    System.out.println("displayed locus"+displayedLocus.sorted)
    val lprox=medium. proximityLocus(displayedLocus.toSet + locusV) //V is allways displayed
    System.out.println(lprox)
    if(medium.planarGraph.suspectBigFaces.nonEmpty) hasBigFaces = hasBigFaces + displayedLocus.sorted
     System.out.println("the following faces are too big: "+medium.planarGraph.suspectBigFaces.mkString(","))
    if(medium.planarGraph.crossingEdge().nonEmpty) { hasCrossedFace = hasCrossedFace+displayedLocus
      System.out.println("we obtain crossed Face with: "+displayedLocus.sorted)
    }
    //  System.out.println("faces are crossing ")//+medium.planarGraph.crossingEdge().mkString(","))

    if(medium.planarGraph.suspectBigFaces.nonEmpty) {
      System.out.println("the following faces are too big: "+medium.planarGraph.suspectBigFaces.mkString(","))
    }
    val ok=medium.voronoise((displayedLocus).toSet + locusV,lprox)
    if(!ok){
      System.out.println("some polygon not set with"+displayedLocus.sorted)
      hasTrou=hasTrou + displayedLocus.sorted
    }
  }
  System.out.println("hascrossed face\n"+hasCrossedFace.mkString("\n"))
  System.out.println("has big face\n"+hasBigFaces.mkString("\n"))
  System.out.println("polygone failed to build, triangles not empty\n"+hasTrou.mkString("\n"))



}
