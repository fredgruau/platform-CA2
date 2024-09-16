package dataStruc
import org.scalatest.{BeforeAndAfter, FunSuite}
import triangulation.Utility.{pop, push}
import triangulation.Vector2D
class PlanarGraphTest extends FunSuite with BeforeAndAfter{


 /** builds a 2D grid of h * times w squares */
 def squares(h:Int, w:Int):PlanarGraph={
  val g=new PlanarGraph
  for(i<-0 to h) for(j<-0 to w){
   val vij=new Coord2D(i,j)
   g.addVertex(vij)
   val vim1j=new Coord2D((i-1).toDouble,j)
   val vijm1=new Coord2D(i,(j-1).toDouble)
   if(i-1>=0)
    g.addEdge(vim1j,vij)
   if(j-1>=0)
    g.addEdge(vijm1,vij)
  }
  g.computeFace()
  g
 }
 test("four square"){
  val g=squares(1,1)
  System.out.println(g)
  assert(g.faces.size==2)
  g.checkInvariant()

 }



 test("six square"){
  val g=squares(1,2)
  System.out.println(g)
  assert(g.faces.size==3)
  g.checkInvariant()
 }

 test("twelve square"){
  val g=squares(2,3)
  System.out.println(g)
  assert(g.faces.size==7)
  g.checkInvariant()
 }

}
