package dataStruc

import dataStruc.Coord2D.triangle
import dataStruc.PlanarGraph.NbFaceMinContour
import triangulation.Utility.angle
import triangulation.{Triangle2D, Utility, Vector2D}

import java.awt.Polygon
import java.awt.geom.Line2D
import scala.::
import scala.collection.immutable.HashSet
import scala.collection.{immutable, mutable}
import scala.swing.Dimension

/** a plannar graph is built from a set of vertices and edges that do not cross ,
 * after that, a method can compute the faces, and then the voronoi region */
class PlanarGraph() {
  /** Edges are identified by their coordinate */
  val vertice: mutable.HashMap[Coord2D, Vertex2] = mutable.HashMap()
  val edges: mutable.HashSet[Edge2] = mutable.HashSet()
  val faces: mutable.HashSet[Face2] = mutable.HashSet()
  //def reset() = {vertice.clear(); edges.clear(); faces.clear(); outerBorder=null}
  def resetEdgesandFaces()={edges.clear(); faces.clear(); outerBorder=null}
  /** one of the face is  the distinguished outerborder  */

  var outerBorder: Face2 = null
  /** the graph is printed by printing all its vertice */
  override def toString = vertice.values.map(_.toString).mkString('\n'.toString)

  /** returns all the edges of the graph which cross another edge thereby compromising planarity */
  def crossingEdge()={
    var res:HashSet[Edge2]=HashSet()
    for(f<-faces) {
      if(f.border.size<31) //we do not consider the outerborder
         res=res.union(f.crossingEdge())
    }
    res;
  }
  def computeFace(): Unit = {
    def sortEdges():Unit={
      for (v <- vertice.values) {
        v.incoming = v.incoming.sorted   //we establish a correspondance between outgoing and incomming,
        v.outGoing=v.incoming.map(_.miror) //outgoing get the same rank as the corresponding incomming
         var rank = 0;
        for (e <- v.incoming) {
          e.rankOfIncomingInTarget = rank; rank += 1 //each edges knows its rank in target
        }
      }
    }
    sortEdges() //will order incoming edges by angles using a nice version of arctan allways defined, converting cartesian to polar.
    val edgesLeft = edges.clone() //we clone all the edges so that we can iterate on a set by gradually removing edges from the set.
    while (edgesLeft.nonEmpty) { //we go through all the edges
      val startEdge = edgesLeft.head
      var current = startEdge
      /** list of edges around the current face */
      var border: List[Edge2] = List()
      do { //we build the border of the right face
        assert(edgesLeft.contains(current), "current is not in edge left") //this is a delicate test, since edge is a case class with mutable data inside
        edgesLeft.remove(current)
        border = current :: border  //the face is identified by a sequence of edges.
        val out = vertice(current.target).outGoing //ougoing edges
        assert(out.nonEmpty)
        val index = (current.rankOfIncomingInTarget + out.length - 1) % out.length //we decrement
        current = out(index)
      } while (current != startEdge)  //when we hit upon the starting edges, that means we have cycled around the face
      val f: Face2 = new Face2(border)
      for (e: Edge2 <- border)
        e.right = f  //we set the face associated to the edge, may be not usefull
      faces += f

      //test if outerborder, we work on simple graph where faces are usually trianglular, and sometimes trapezoidal with four neighbors.
      setOuterBorder()
    }


  }

  def setOuterBorder()={
    for(f<-faces)
      if (f.border.size > NbFaceMinContour) {
        f.outerBorder = true
        outerBorder = f
      }
  }

  def addVertex(c: Coord2D) =
    vertice += c -> Vertex2(c)

  /**
   *
   * @param src source vertice
   * @param target target vertice
   * @return add edges from source to target, and also from target to source if not created yet, and links the two using the miror field of edges.
   */
  def addEdge(src: Coord2D, target: Coord2D): Edge2 = {
    val e = Edge2(src, target)
    if (!edges.contains(e)) {
      edges += e
      vertice(src).outGoing = vertice(src).outGoing :+ e //this is not really usefull, since we will recompute the outgoing list from the incoming using miror
      vertice(target).incoming = vertice(target).incoming :+ e
      val m=addEdge(target, src) //build miror edge if needed.
      if (m!=null) {e.miror=m; m.miror=e}
      e
    }
    else null
  }

  /** we assume that inner face are either trinagle or trapeze, we also will set outgoing following incomming */
  def checkInvariant() = {
    for (f <- faces)
      assert(f.border.size <= 30 || f.outerBorder)
    for(v<-vertice.values)
      v.invariantOutGoing()

  }

  /** used for debug, shoud retrun a big list for 3, and 4, and then the exterior border */
  def histo: Seq[(Int, Int)] = {
    val h = faces.toList.map(_.border.size)
    .groupBy(x=>x)
    val h2=h.map(x=>x._1->x._2.size)
    .toSeq
    .sortBy(x=>x._1)
    //.map(x=>x._2)
    h2
  }
  /** discard the outer face, which is the biggest,  */
  def suspectBigFaces={
    val faceSize=faces.toList.map(_.border.size).toSet.toSeq.sorted
    faceSize.reverse.tail.filter(_>6)
  }


}

/** we redefine vector2D in order to have a case class */
case class Coord2D(x:Double,y:Double){
  def sub(c2:Coord2D)=Coord2D(x-c2.x, y-c2.y)
  def prodScal(c:Coord2D)=x*c.x+y*c.y
  def norme=Math.sqrt(x*x+y*y)
  def toVector2D=new Vector2D(x.toDouble,y.toDouble)
  override def toString="x:"+x+" y:"+y
}
object Coord2D{
  def triangle(c1: Coord2D,c2:Coord2D,c3:Coord2D):Triangle2D=new Triangle2D(new Vector2D(c1.x,c1.y),new Vector2D(c2.x,c2.y),new Vector2D(c3.x,c3.y))
}
//on a sortit les classes pour faire des test, on pourra les re-rentrer aprés.
case class Vertex2( coord:Coord2D){
  /** edges which are incoming and should be sorted */
  var incoming:Vector[Edge2]=Vector()
  var outGoing:Vector[Edge2]=Vector()
  override def toString={
    //def edgesString(ve:Vector[Edge2]):String=ve.mkString(" ")
    coord.x +"_"+ coord.y +" incomming "+incoming.mkString(" ")+"outgoing "+outGoing.mkString(" ") //liste des voisins en entrée suivi de ceux en sortie?
  }
  /** outgoing can be found from incomming */
  def invariantOutGoing()={
    for(i <- 0 until incoming.size)
      assert(incoming(i).isSymetric(outGoing(i)))  // outgoing and incomming of rank i, are mirored
  }
}
case class Edge2( src:Coord2D, target:Coord2D) extends Ordered[Edge2]{
  //rank of the edge among the target
  def isSymetric(e:Edge2):Boolean={
    src.equals(e.target)&& target.equals(e.src)
  }
  def vect=target.sub(src)
  def angle=Math.atan2(vect.y,vect.x)
  /** will enable to follow the left border */
  var rankOfIncomingInTarget= -1
  var right:Face2=null
  /** we need to access the miror edge */
  var miror:Edge2=null
  /** compare the angles in trigonometric order */
  override def compare(that: Edge2): Int = (10000000*(angle-that.angle)).toInt//1000000* vect.dot(that.vect).toInt
  /** we print the vector pointing to target, for compactness */
  override def toString= "x="+ vect.x + " y=" +vect.y + ","

  /** true if one of the edges intersects */
  def intersect(edges: Set[Edge2]): Boolean = {
    for (e<-edges)
      if(intersectOne(e)) return true
    return false
  }
  /** true if segments associated to edges intersect */
  def intersectOne(e:Edge2)={!touching(e)&&
    Line2D.linesIntersect(src.x,src.y,target.x,target.y,e.src.x,e.src.y,e.target.x,e.target.y)
  }

  def touching(e:Edge2): Boolean ={src==e.src||  src==e.target|| target==e.src||target==e.target}


}
class Face2(val border:List[Edge2]){
  /**  build the polygon associated to the face  */
  def toPolygon:Polygon=Utility.toPolygon(border.map(_.src.toVector2D))
  var outerBorder = false
  var isCrossing  = false
  def triangles:List[Triangle2D]=
    {
      border.size match {
      case 3 => List(new Triangle2D(border(0).src.toVector2D,border(1).src.toVector2D,border(2).src.toVector2D))
      case 4=>  //we have a trapeze, which is split in two triangles.
        val A=border(0).src;val B=border(1).src; val C=border(2).src;val D=border(3).src
        val somme=angle(A,B,C)+angle(C,D,A)
        if (somme > Math.PI)
          List(new Triangle2D(A.toVector2D,B.toVector2D,D.toVector2D),new Triangle2D(C.toVector2D,B.toVector2D,D.toVector2D))//we cut along BD
        else
          List(new Triangle2D(B.toVector2D,A.toVector2D,C.toVector2D),new Triangle2D(D.toVector2D,A.toVector2D,C.toVector2D)) //we cut along AC
      case 5 =>  //we look for the biggest angle
        val border2=border(4)::border:::List(border(0))
        val angles=(1 to 5).map((i:Int)=>angle(border2(i-1).src,border2(i).src ,border2(i+1).src))
        val sortedAngle=angles.sorted
        val indexMin1=angles.indexOf(sortedAngle(0))+1
        val indexMin2=angles.indexOf(sortedAngle(1))+1
        //we decide between two situation: the two mins are contiguous or not
        val d=Math.abs(indexMin1-indexMin2)
        val contiguous=HashSet(1,4).contains(d) //diff will be 4 if they are separted.
        if(contiguous){
          val shiftedB=if(d==4) border
          else (0 to 4).map((i:Int)=>border((i+4-Math.min(indexMin1,indexMin2))%5))
          val triangle1=triangle(shiftedB(1).src,shiftedB(2).src,shiftedB(3).src)
          val triangle2=triangle(shiftedB(1).src,shiftedB(0).src,shiftedB(3).src)
          val triangle3=triangle(shiftedB(4).src,shiftedB(0).src,shiftedB(3).src)
          List(triangle1, triangle2,triangle3)
        }
        else {
       /* val triangle1=triangle(border2(indexMin1-1).src,border2(indexMin1).src,border2(indexMin1+1).src)
        val triangle2=triangle(border2(indexMin2-1).src,border2(indexMin2).src,border2(indexMin2+1).src)
        val otherInd=(1 to 5).toSet.diff(HashSet(indexMin1,indexMin2)) //other index than the two minimum
        val otherPoint=otherInd.map(border2(_)).toSeq
        val triangle3=triangle(otherPoint(0).src,otherPoint(1).src,otherPoint(2).src)*/
       //however we can also have a square, in which case the extremity should be chose among those with biggest angle. We generate this approach
       val im= angles.indexOf(sortedAngle(4)) //lies between 0 and 5

          val triangle1=triangle(border(im).src,border((im+1)%5).src,border((im+2)%5).src)
          val triangle2=triangle(border(im).src,border((im+2)%5).src,border((im+3)%5).src)
          val triangle3=triangle(border(im).src,border((im+3)%5).src,border((im+4)%5).src)

        List(triangle1, triangle2,triangle3)}
      case 6 => //if we have a perfect hexagon, all the triangle can originates from one extremity (that 's a bit surprising)
        //however we can also have a square, in which case the extremity should be chose among those with biggest angle. We generate this approach
        val border2=border(5)::border:::List(border(0))
        val angles=(1 to 6).map((i:Int)=>angle(border2(i-1).src,border2(i).src ,border2(i+1).src))
        val sortedAngle=angles.sorted
        val im=angles.indexOf(sortedAngle(5)) //lies between 0 and 5

        val triangle1=triangle(border(im).src,border((im+1)%6).src,border((im+2)%6).src)
        val triangle2=triangle(border(im).src,border((im+2)%6).src,border((im+3)%6).src)
        val triangle3=triangle(border(im).src,border((im+3)%6).src,border((im+4)%6).src)
        val triangle4=triangle(border(im).src,border((im+4)%6).src,border((im+5)%6).src)

       /* val triangle1=triangle(border(0).src,border(1).src,border(2).src)
    val triangle2=triangle(border(0).src,border(2).src,border(3).src)
    val triangle3=triangle(border(0).src,border(3).src,border(4).src)
    val triangle4=triangle(border(0).src,border(4).src,border(5).src)*/
        List(triangle1, triangle2,triangle3,triangle4)

      case _ => List() //other faces is only the outer face.
    }

    }
  /** a face is non plannar if it contains both an edge and its opposite. */
   def nonPlannar():Boolean =
    { for(e<-border)
        if(border.contains(e.miror)||e.intersect(border.toSet.diff(HashSet(e))))
            return true
      return false
    }

  /** a face is non plannar if it contains both an edge and its opposite. */
  def crossingEdge():HashSet[Edge2] =
  { var res:immutable.HashSet[Edge2]=immutable.HashSet()
    for(e<-border)
    if(border.contains(e.miror)||e.intersect(border.toSet.diff(HashSet(e))))
    {
      res=res+e
      isCrossing=true
    }
    return res
  }

}
object PlanarGraph{
  val NbFaceMinContour=17 //face will be contour if bordersize bigger than 17
}
