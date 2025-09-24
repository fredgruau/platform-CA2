package simulator
//import DelaunayLogic.{Delaunay, QuadEdge}
//import GeometricPrimitives.FinitePoint
import Medium.add2
import dataStruc.Util.{Rectangle, border, copyArray, sameElements}
import simulator.CAtype.pointLines
import triangulation.Vector2D
import compiler.Locus.{allLocus, locusE, locusEf, locusEv, locusF, locusFe, locusFv, locusV, locusVe, locusVf}
import compiler.{T, _}
import dataStruc.{Coord2D, PlanarGraph}
import simulator.{InitSelect, encodeByInt, encodeGt, encodeLt}
import triangulation.{DelaunayTriangulator, NotEnoughPointsException, Triangle2D, Vector2D, Voroonoi}

import java.util
import scala.::
import scala.collection.IterableOnce.iterableOnceExtensionMethods
import scala.collection.immutable.{HashMap, Map}
import scala.collection.{immutable, mutable}
import scala.math.cos
//import de.alsclo.voronoi.graph.Voronoi
import simulator.CAtype.pointLines
import simulator.UtilBitJava.{moveBitxtoy, propagateBit14and1, propagateBit6and1, propagateBitxand1}
import simulator.{Controller, Env, PrShift, UtilBitJava}
import triangulation.Utility._

import java.awt.Color
import scala.collection.IterableOnce.iterableOnceExtensionMethods
import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.mutable.HashMap
import scala.math.{min, random, round}
import scala.swing.Dimension
import scala.swing.Swing.pair2Dimension

/**
 *
 * Provide a partition in 2D space into polygon, for representing the state of the medium
 * locus are distributed in lines, thus having 2 integer coordinates,
 * vertices are displayed from the start
 * together with a neighborood relationship between locus for computing communication during transfers
 *
 * @param nbCol       max number of points per line
 * @param nbLine      number of lines
 * @param boundingBox Rectangles containing all the points, normally it is also exactly the dimension of the CA pannel.
 * @param vertice     location of the vertices (where the real processing elements are located)
 * @param neighborsAbs   encodes the whole architecture of the medium
 *                    by listing the absolute coordinates of the neighbors
 *
 */
abstract class Medium(val nbLine: Int, val nbCol: Int, val boundingBox: Dimension,
                      val vertice: pointLines, val neighborsAbs: Array[Array[Array[(Int, Int)]]] )
  extends  Rectangle with border {
  /** contains the information about faces. */
  var planarGraph=new PlanarGraph
  /** contains points associated to all locus, locus by locus, each point line is a plane,
   * the number of pointlines for a given locus corresponds to the locus density,
   * the ordedr of point lines for a given locus is standardized and the standard is specified
   * the arangment is such that broadcasting is done by doubling or tripling the value
   * which means that all the T neighbors of a given simplicial site are stacked in sequence */
  var locusPlane: immutable.HashMap[Locus, Array[pointLines]]= immutable.HashMap.empty++allLocus.map (l=>(l->Array.ofDim[Option[Vector2D]](l.density, nbLine, nbCol)))/** encodes the neighborhood relation ship between the voronoi"s of points */
  locusPlane(V())(0)=vertice
  //on pensait que tout les vertices sans triangle etaient les corners, mais peut y en avoir qq autres.
 // val cornerUpLeft=vertice(0)(0).get   val cornerDownRight=vertice(vertice.length-1)(vertice(0).length-1).get   val corners=HashSet(cornerDownRight,cornerUpLeft)
  def addToNeighbor(h:mutable.HashMap[Vector2D,Set[Vector2D]], v1:Vector2D, v2:Vector2D)= {
    if(!h.contains(v1))
      h += (v1->HashSet.empty)
    h += (v1->(h(v1) + v2))

  }
  def addToNeighbors(h:mutable.HashMap[Vector2D,Set[Vector2D]], v:Vector2D, s:Set[Vector2D])= s.map(addToNeighbor(h,v,_))

    private def setAsNeighbor(h:mutable.HashMap[Vector2D, Vector2D], v: Option[Vector2D], v2: Option[Vector2D]) =
    if(v.isDefined && v2.isDefined)
      h+=v.get->v2.get
  private def addToNeighbor2(h: mutable.HashMap[Vector2D, Set[Vector2D]], v: Option[Vector2D], v2: Option[Vector2D]) =
    if(v.isDefined&&v2.isDefined) addToNeighbor(h,v.get,v2.get)




  //variables set once for all, independently of which locus is shown or not, used to compute neighborhood
  private var reduc:mutable.HashMap[Vector2D,Vector2D]=mutable.HashMap.empty
  private var clock:mutable.HashMap[Vector2D,Vector2D]=mutable.HashMap.empty
  private var anticlock:mutable.HashMap[Vector2D,Vector2D]=mutable.HashMap.empty
  private var transfer:mutable.HashMap[Vector2D,Vector2D]=mutable.HashMap.empty
  private var bcast:immutable.HashMap[S, mutable.Map[Vector2D,Set[Vector2D]]]=immutable.HashMap.empty

  /** computes the centers of all locus points,  and also the list of neighbors with respect to communication: broadcast, reduce, transfer, clock
 * @param lociProx voronoi adjacency relation between loci, has to be re-computed from the Controller, when locus change
 * all the points are added as vertice of the planar graph,
   * this is called a single time, upon medium's creation.
 *
 * */
  def middleClosure()={
    var broadcastE:mutable.HashMap[Vector2D,Set[Vector2D]]=mutable.HashMap.empty
    var broadcastF:mutable.HashMap[Vector2D,Set[Vector2D]]=mutable.HashMap.empty
    var broadcastV:mutable.HashMap[Vector2D,Set[Vector2D]]=mutable.HashMap.empty


    /**
     *
     * @param neighbors set of possibly non defined points
     * @return barycenter if all points are defined, else non defined
     */
    def barycenter(neighbors:List[Option[Vector2D]]):Option[Vector2D]={
      var res=new Vector2D(0,0)
      for(neighbor<-neighbors) {
        if (neighbor.isEmpty) return None
        res=res.add(neighbor.get)
      }
      Some(res.mult(1.0/neighbors.length))
    }

     def setAsMiddleN(center:Vector2D,neighbors:List[Option[Vector2D]],coeff:Double):Option[Vector2D]={
      val m=barycenter(neighbors)
      if (m.isEmpty) return None
      val m2: Vector2D =center.barycenter(m.get,coeff)
      return Some(m2)
    }
    def setAsMiddle(center:Vector2D,neighbor:Option[Vector2D],coeff:Double):Option[Vector2D]=
         setAsMiddleN(center,List(neighbor),coeff)
    def setAsMiddleO(center:Option[Vector2D],neighbor:Option[Vector2D],coeff:Double):Option[Vector2D]=
      if(center.isEmpty) None else setAsMiddle(center.get,neighbor, coeff)
    def tryFind2(l:Locus,d:Int,i:Int,j:Int): Option[Vector2D] = if (!inside(i,j)) None   else locusPlane(l)(d)(i)(j)
    def v(tuple: (Int, Int)) = tryFind2(V(),0,tuple._1,tuple._2)
    def f(d: Int, i: Int, j: Int) = tryFind2(F(),d,i,j)
    def e(d: Int, i: Int, j: Int) = tryFind2(E(),d,i,j) //point of edge toward direction d
    def tev(d: Int, i: Int, j: Int) = tryFind2(T(E(),V()),d,i,j) //point of Ev toward direction d
    def tfv(d: Int, i: Int, j: Int) = tryFind2(T(F(),V()),d,i,j) //point of Fv  toward direction d
    def tfe(d: Int, i: Int, j: Int) = tryFind2(T(F(),E()),d,i,j) //point of Fv  toward direction d
    def vOFv(d:Int,i:Int,j:Int)=v(neighborsAbs(d)(i)(j))
    /**
     *
     * @param d neighbor index between 0 and 5
     * @param i x coordinate
     * @param j y coordinate
     * @return the point representing the neighbor edge, if that edge exists
     *         we distinguish the case d<3 in which case the edge can be accessed directly
     *         from the case d=3,4,5 in which case we have to first see if neighbor is defined and if so, take it d-3 edge
     * */
    def eOFV(d: Int, i: Int, j: Int): Option[Vector2D] = {
      if (d < 3) locusPlane(E())(d)(i)(j)
      else {
        val n: (Int, Int) = neighborsAbs(d)(i)(j)
        if(v(n).isDefined)   locusPlane(E())(d - 3)(n._1)(n._2)    else None
      }
    }

    /** the two vertice associated to an edge; if orientation is null return vertex at i,j else return neighbor vertex along d */
    def vOFe(d: Int, o: Int, i: Int, j: Int): Option[Vector2D] = if (o == 0) vertice(i)(j)   else  vOFv(d,i,j)

    for (i <- 0 until nbLine)//first we compute coordinates of  simplicial loci V,E,F
      for (j <- 0 until nbCol)
        {for (dir <- 0 until 3) //Locus E
            locusPlane(E())(dir)(i)(j) = setAsMiddle(v(i,j).get, vOFv(dir,i,j), 0.5)
          for (dir <- 0 until 2) //Locus F
            locusPlane(F())(dir)(i)(j) = setAsMiddleN(v(i,j).get, List(neighborsAbs(dir)(i)(j), neighborsAbs(dir + 1)(i)(j)).map(v(_)), 1.0 / 3.0)
        }

    for (i <- 0 until nbLine) {//then we computes coordinates of transfer loci which uses simplicial loci
      for (j <- 0 until nbCol) {
        val v = vertice(i)(j).get
        val jup = if (i % 2 == 1) j else j - 1
        val fOFv = List(f(0, i, j), f(1, i, j), f(0, i, j - 1), f(1, i - 1, jup), f(0, i - 1, jup), f(1, i - 1, jup + 1)) //the 6 neighbor faces  se,s,sw,nw,n,ne of a vertice v, in the order se,s,sw,nw,n,ne
        val vOFf = List(vOFv(1, i, j), vOFv(0, i, j), vertice(i)(j), vertice(i)(j), vOFv(2, i, j), vOFv(1, i, j)) //the 6 neigbor vertices of a faces  dp,db1,db1,up,ub1,ub2
        val fOFe = List(f(1, i - 1, jup + 1), f(0, i, j), f(1, i, j), f(0, i, j - 1)) //the four faces sandwiching the three edges
        val eOFf = List(e(0, i, j), e(2, i, j + 1), e(1, i, j), e(0, i + 1, jup), e(2, i, j), e(1, i, j)) //edge adjacent to db,ds1,ds1,ub,us1,us2
        for (dir <- 0 until 6) //iteration on the 6 site of each transfer loci Ve,Ev, Vf, Fv
        {  addToNeighbor2(broadcastV,Some(v),vOFv(dir,i,j)) //we assume vertice can do a broadcastV if there is only vertice

          val tVe=setAsMiddle(v, eOFV(dir, i, j), 2.0 / 3.0)
          locusPlane(T(V(), E()))(dir)(i)(j) = tVe
          addToNeighbor2(broadcastE,Some(v),tVe)
          setAsNeighbor(reduc,tVe,Some(v))
          val tEv= setAsMiddleO(eOFV(dir / 2, i, j), vOFe(dir / 2, dir % 2, i, j), 2.0 / 3.0)
          locusPlane(T(E(), V()))(dir)(i)(j) =tEv
          addToNeighbor2(broadcastV,eOFV(dir / 2, i, j),tEv) //connection de E vers Ev
          setAsNeighbor(reduc,tEv,eOFV(dir / 2, i, j) )

          val tVf= setAsMiddle(v, fOFv(dir), 2.0 / 3.0) //Vf
          locusPlane(T(V(), F()))(dir)(i)(j) = tVf
          addToNeighbor2(broadcastF,Some(v),tVf)
          setAsNeighbor(reduc,tVf,Some(v))
          val f=locusPlane(F())(dir / 3)(i)(j) //pt associé a la face courante
          val tFv=setAsMiddleO(f, vOFf(dir), 2.0 / 3.0) //Fv
          locusPlane(T(F(), V()))(dir)(i)(j) = tFv
          addToNeighbor2(broadcastV,f,tFv)//connection de F vers Fv
          setAsNeighbor(reduc,tFv,f )

          val tEf=setAsMiddleO(locusPlane(E())(dir / 2)(i)(j), fOFe(dir / 2 + dir % 2), 2.0 / 3.0) //Ef
          locusPlane(T(E(), F()))(dir)(i)(j) = tEf
          val e=locusPlane(E())(dir / 2)(i)(j)
          addToNeighbor2(broadcastF,e,tEf)
          setAsNeighbor(reduc,tEf,e)
          val tFe=setAsMiddleO(locusPlane(F())(dir / 3)(i)(j), eOFf(dir), 2.0 / 3.0)
          locusPlane(T(F(), E()))(dir)(i)(j) = tFe
          addToNeighbor2(broadcastE,f,tFe)//connection de F vers Fv
          setAsNeighbor(reduc,tFe,f )
        }
      }
    }
    for(i<-0 until nbLine) //we now compute the transfer neighborhood, which uses the coordiunates of transfer points.
      for(j<-0 until nbCol){
        val jup = if (i % 2 == 1) j else j - 1
        val tEvOFv=List(tev(0,i,j),tev(2,i,j),tev(4,i,j),tev(1,i,j-1),tev(3,i-1,jup) ,tev(5,i-1,jup+1)) //the six TEv connecting to the Tves of one vertice
        val tFvOFv=List(tfv(2,i,j),tfv(3,i,j),tfv(1,i,j-1),  tfv(5,i-1,jup),tfv(0,i-1,jup) ,tfv(4,i-1,jup+1)) //the six TFv connecting to the Tvfs of one vertice
        val tFeOFe=List(tfe(3,i-1,jup+1),tfe(0,i,j),tfe(2,i,j),  tfe(5,i,j),tfe(4,i,j) ,tfe(1,i,j-1)) //the six TFv connecting to the Tvfs of one vertice

        for (dir<-0 until 6){
         //set all the transfers
          def tVe(d:Int)=locusPlane(T(V(), E()))(d)(i)(j)
          setAsNeighbor(transfer,tVe(dir),tEvOFv(dir))
          setAsNeighbor(transfer,tEvOFv(dir),tVe(dir))
         def tVf(d:Int)=locusPlane(T(V(), F()))(d)(i)(j)
          setAsNeighbor(transfer,tVf(dir),tFvOFv(dir))
          setAsNeighbor(transfer,tFvOFv(dir),tVf(dir))
          def tEf(d:Int)=locusPlane(T(E(), F()))(d)(i)(j)
          setAsNeighbor(transfer,tEf(dir),tFeOFe(dir))
          setAsNeighbor(transfer,tFeOFe(dir),tEf(dir))
          //set all the rotations,
          val dp1=(dir+1)%6
          //rotation around E
          val dm1=(dir+5)%6
          setAsNeighbor(clock,tVe(dir),tVf(dir) )
          setAsNeighbor(anticlock,tVe(dir),tVf(dm1) )
          setAsNeighbor(clock,tVf(dir),tVe(dp1) )
          setAsNeighbor(anticlock,tVf(dir),tVe(dir))
          //rotation around E
          val dnew=(dir+1)%2+2*(dir/2)
          assert(Math.abs(dnew-dir)==1)
          def tEv(d:Int)=locusPlane(T(E(), V()))(d)(i)(j)
          setAsNeighbor(clock,tEv(dir),tEf(dir) )
          setAsNeighbor(anticlock,tEv(dir),tEf(dnew) )
          setAsNeighbor(anticlock,tEf(dir),tEv(dir) )
          setAsNeighbor(clock,tEf(dnew),tEv(dir))
          //rotation around F
          def tFv(d:Int)=locusPlane(T(F(), V()))(d)(i)(j)
          def tFe(d:Int)=locusPlane(T(F(), E()))(d)(i)(j)
          val dp=(6-dir+2)%3+3*(dir/3)
          val dm=(6-dir+1)%3+3*(dir/3)
           setAsNeighbor(clock,tFv(dir),tFe(dm) )
           setAsNeighbor(anticlock,tFv(dir),tFe(dp) )
           setAsNeighbor(anticlock,tFe(dm),tFv(dir) )
           setAsNeighbor(clock,tFe(dp), tFv(dir))
        }
      }
    bcast=immutable.HashMap(V()->broadcastV,E()->broadcastE,F()->broadcastF)
    checkInvariant

    //ensureUniqueDisplayedPoint()
    /** adds the CA points in the graph */
    //planarGraph.reset()
    for(l<-Locus.allLocus){
      val s=pointSet(l)
      for(p: Vector2D <-s)
        planarGraph.addVertex(dataStruc.Coord2D(p.x,p.y))  //we add the points of all locux, a single time.
    }

  }

  middleClosure()

  def checkInvariant={
      for(l<-List(T(V(),E()),T(E(),V()),T(V(),F()),T(F(),V()),T(E(),F()),T(F(),E())))
    {
      for (p<-pointSet(l)){
        assert(transfer.contains(p)) //transfer est défini partout sur les locus de transfer
        assert(transfer.contains(transfer(p)))
        assert(transfer(transfer(p))==p) //tranfer est idempotent
        if(clock.contains(p))
          assert(anticlock(clock(p))==p)
      }
      for(l:Locus<-List(V(),E(),F()))
        for (p<-pointSet(l))
          for(l2<-List(V(),E(),F()))
        { if(l2!=l) {
          assert(bcast(l2).contains(p))  //simplicial locus can broadcast
          val p2s: Set[Vector2D] =bcast(l2)(p)
          for(p2<-p2s){
            assert(reduc.contains(p2)) //reduction will be defined
            assert(transfer.contains(p2)) //transfer est défini partout sur les locus de transfer
            assert(reduc.contains(transfer(p2)))
            assert(reduc(p2)==p) //and it is the inverse
          }
        }
        }
    }
  }
 ///** for each vertex, containes the neighbor vertices. */
 // var locusNeighbors: mutable.HashMap[Vector2D, Set[Vector2D]]=mutable.HashMap.empty //we initialize it correctly in middleClosure
  /** contains also the graph of vornoi adjacecency, is able to build the face, so as to derive the triangles */



  def red(points: Set[Vector2D]): Set[Vector2D] =
    points.filter(reduc.contains(_)).map(reduc)//.foldLeft(HashSet.empty,((acc:Set[Vector2D], elem:Vector2D) => acc.union(elem))

  def trf(points: Set[Vector2D]): Set[Vector2D] =
    points.filter(transfer.contains(_)).map(transfer)

  /**
   *
    * @param v point
   * @return neighbor withs repects to clock and anticlock there can be O,1, or 2 such neighbors.
   */
  def rot(v:Vector2D):Set[Vector2D]={
    val res:mutable.HashSet[Vector2D]=mutable.HashSet.empty
    if(clock.contains(v))
      res+=clock(v)
    if(anticlock.contains(v))
      res+=anticlock(v)
    res.toSet
  }
  def rot2(v:Vector2D):Set[Vector2D]={
    val res:mutable.HashSet[Vector2D]=mutable.HashSet.empty
    if(clock.contains(v)&&clock.contains(clock(v)))
      res+=clock(clock(v))
    if(anticlock.contains(v)&&anticlock.contains(anticlock(v)))
      res+=anticlock(anticlock(v))
    res.toSet
  }

  def rot2s(vs:Set[Vector2D]):Set[Vector2D]=vs.map(rot2(_)).flatten






  /**
   *
   * @param lociProx graph of locus adjacency
   * "leverage" the graph from locus-graph to point-graph, using neighborhood of broadcast,transfer, reduce, clock
   * this function has to be called each time a change of displayed locus is done.
   */

 def computeNeighbors(lociProx:Map[Locus,Set[Locus]])= {
   def addAllPoints()={
     for(l<-Locus.allLocus)
       for(p: Vector2D <-pointSet(l))
         planarGraph.addVertex(dataStruc.Coord2D(p.x,p.y))  //we add the points of all locux, a single time.
   }
  //  locusNeighbors=mutable.HashMap.empty //locusNeighbor obsolete, it is plannar graph which is used now.
   //resetLocusNeigbors
   planarGraph.resetEdgesandFaces()  //we forget edges and faces, in case  we are recomputing new edges and faces
   planarGraph.vertice.clear()
   addAllPoints()
   val i=1
   def adds(v:Vector2D, se:Set[Vector2D])={
    // addToNeighbors(locusNeighbors,v,se)
     //using graph
     for(v2<-se) planarGraph.addEdge(Coord2D(v.x,v.y),Coord2D(v2.x,v2.y))
   }
   def add(v:Vector2D, v2:Vector2D)= {
    // addToNeighbor(locusNeighbors,v,v2)
     //using graph
     planarGraph.addEdge(Coord2D(v.x,v.y),Coord2D(v2.x,v2.y))
   }
   for ((l, loci: Set[Locus]) <- lociProx) { //on va rajouter progressivement tout les voisinages possibles.
     def notAdjacent( ls:Locus*):Boolean= ls.filter(loci.contains(_)).isEmpty
      for (lvois <- loci) //lvois is neibhor of l
           (l, lvois) match {
             case (V(),V() )=>for (v <- pointSet(V())) adds(v,bcast(V())(v)) //only vertice are here
             case (E(),E() )=>for (v <- pointSet(E())) {
               if(notAdjacent(locusF,locusEf,locusFe,locusFv))   adds(v,red(trf(rot2s(trf(bcast(locusV)(v))))) )//links around F
             }
             case (F(),F() )=>for (v <- pointSet(F())) {
            //   if(notAdjacent(locusF,locusEf,locusFe,locusFv))   adds(v,red(trf(rot2s(trf(bcast(locusF)(v))))) )//links around F
               if(notAdjacent(locusE,locusEf,locusEv,locusFv,locusFe) ) {
                 val vs=red(trf(rot2s(trf(bcast(locusV)(v)))))
                 adds(v,vs)  //links around V
               }
             } //only vertice are here
             case (s1: S, s2: S) =>
               for (v <- pointSet(l))
                 adds( v, red(trf(bcast(s2)(v)))) //direct neighborhood between simplicial locus
             //case (s: S,  T(s1,s2)) =>   for(v <-pointSet(l)) symetric
              // if(s1==s)adds(v, bcast(s2)(v))
              //  else  if(s2==s)  adds(v, trf(bcast(s1)(v)))
             //else adds( v,trf(bcast(s1)(v))) //s,s1 and s2 are all distinct


             case ( T(s1,s2),s: S) =>  for(v <-pointSet(l)) {
               if(s1==s) add(v, reduc(v))
               else  if(s2==s)   add(v, reduc(transfer(v)))
               else adds(v, red(trf(rot(v))))//s1,  s2 and s are all distinct
                // adds(v, red(trf(bcast(s)(reduc(v)))))// erronné, rajoute trop de connec


             }


             case (T(E(),V()),T(E(),V())) =>for(v <-pointSet(l)) {
                if(!loci.contains(E()))  adds(v,rot2(v))  //conecte en face
               if(!loci.contains(T(F(),V())))   adds(v, trf(rot2(transfer(v)))) //connecte autour de V
             }
             case (T(V(),E()),T(V(),E())) =>for(v <-pointSet(l)) {
                 if(!loci.contains(T(V(),F()))) //Ve goes around V
                   adds(v,rot2(v))
                 if( loci.intersect(HashSet(locusEv,locusFe,locusFv,locusE,locusF)).isEmpty)
                   adds(v, trf(rot2(transfer(v))))
               }
             case (T(F(),V()),T(F(),V())) =>for(v <-pointSet(l)) {
               if(!loci.contains(locusFe) && !loci.contains(locusEf))
                 adds(v,rot2(v))
               if(!loci.contains(locusEv))
                 adds(v, trf(rot2(transfer(v))))
             }
             case (T(V(),F()),T(V(),F())) =>for(v <-pointSet(l)) {
               if(notAdjacent(locusVe) )    adds(v,rot2(v)) //links around V
               if(notAdjacent(locusE,locusF,locusEf,locusFe,locusEv,locusFv))      adds(v, trf(rot2(transfer(v)))) //links around F
             }

             case (T(F(),E()),T(F(),E())) =>for(v <-pointSet(l)) {
               //if(!loci.contains(locusFv)&& !loci.contains(locusVf))
                 adds(v,rot2(v))
              // if(!loci.contains(locusEv)) adds(v, trf(rot2(transfer(v))))
              // if(!loci.contains(locusEf)) adds(v, trf(rot2(transfer(v))))
             }
             case (T(E(),F()),T(E(),F())) =>for(v <-pointSet(l)) {
               if(!loci.contains(locusEv)&& !loci.contains(locusVe)&& !loci.contains(locusE))
                 adds(v,rot2(v))
               if(!loci.contains(locusFv))
                 adds(v, trf(rot2(transfer(v))))
             }


             case ( T(s1,s2),T(s3,s4)) => for(v <-pointSet(l)) {
               if(s1==s4&&s2==s3)  add(v, transfer(v))
               else if (s1==s3 && !HashSet(s1,s2).contains(s4))  //s4 is a third
                 adds(v, rot(v))
               else if (s1==s4 && !HashSet(s1,s2).contains(s3)) {
                 val vs=trf(rot(v))
                 adds(v,vs )
               }
               else if(s2==s4 && s1!=s3) //faut tourner autour de s2=s4, pour ca faire un transfer aller et un transfer retour.
                 {adds(v, trf(rot(transfer(v))))

                 }
             }
             case _ => //pour avaler les cas symmétrique
            }
   }
   planarGraph.computeFace()  //now that we have all the edges, we can compute the faces.
   planarGraph.checkInvariant()  //we could check the crossed Faces
   //System.out.println(planarGraph.histo)

 }

/*
  /**
   *  set the neighbors to empty
   */
  def resetLocusNeigbors= //a virer
    for(p<-displayedPoint)
      if(!locusNeighbors.contains(p))
        locusNeighbors += (p->HashSet.empty)*/
  /** all the voronoi's polygons plus features */
  //var voronoi: immutable.HashMap[Vector2D, Voroonoi] = immutable.HashMap()
  var theVoronois: immutable.HashMap[Coord2D, Voroonoi] = immutable.HashMap()
  /** points  being displayed (whose voronoi are colored) */
  var displayedPoint: Set[Vector2D] = Set()
   var triangleSoupDelaunay:List[Triangle2D] = null
  var triangleSoup:List[Triangle2D] = null

  /**
   *
   * @param L currently displayed locus
   *          resets the colors and texts of the voronois
   */
  def resetColorTextVoronoi(L: Set[Locus]): Unit =
    for (l <- L)
      for (points2D: pointLines <- locusPlane(l))
        for (i <- 0 until nbLine)
          for (j <- 0 until nbCol) {
            val point: Option[Vector2D] = points2D(i)(j) //corresponding point in 2D space
            if (point.isDefined)
              theVoronois(Coord2D(point.get.x,point.get.y)).resetColorText() //updating voronoi's polygon color
          }


  /**
   * sum to the colors of locus l, the contribution of bitplanes
   * which can represent a boolean field
   *
 *
   * @param color     color to be summed
   * @param bitPlane whether or not it should be summed
   * @param points where it should be summed
   * @param darkness integer defined by the controller, between 0 and 255
   */
  def sumColorVoronoi(color: Color, bitPlane:Array[Array[Boolean]], points:pointLines,darkness:Int): Unit = {
    assert (points.size == nbLine, "pointlines should match CA")
    assert (bitPlane.size == nbLine, "number of  lines should match CA")
     for (i <- 0 until nbLine)  for (j <- 0 until nbCol)
          if (bitPlane(i)(j)) { //the field is present, its color must contribute to the voronoi polygon's color
            val point = points(i)(j) //corresponding point in 2D space
            // assert(point!=None,"we should have defined the color of non existing points")
            if (point.isDefined)
              theVoronois(Coord2D(point.get.x,point.get.y)).addColor(color,darkness) //updating voronoi's polygon color
          }
    }
  /**
   * sum to the colors of locus l, the contribution of bitplanes
   * which can represent a boolean field
   * @param text    text to be displayed
   * @param bitPlane whether or not it should be summed
   * @param points where it should be summed
   */
  def sumBitVoronoi( bitPlane:Array[Array[Boolean]], points:pointLines): Unit = {
    assert (points.size == nbLine, "pointlines should match CA")
    assert (bitPlane.size == nbLine, "number of  lines should match CA")
    for (i <- 0 until nbLine)  for (j <- 0 until nbCol) {
      val point = points(i)(j) //corresponding point in 2D space
      // assert(point!=None,"we should have defined the color of non existing points")
      if (point.isDefined)
        theVoronois(Coord2D(point.get.x, point.get.y)).addBit(bitPlane(i)(j)) //updating voronoi's polygon color
    }
  }

  def textify(  points:pointLines,ls:List[String]): Unit =
     for (i <- 0 until nbLine)  for (j <- 0 until nbCol) {
      val point = points(i)(j) //corresponding point in 2D space
      // assert(point!=None,"we should have defined the color of non existing points")
      if (point.isDefined)
        theVoronois(Coord2D(point.get.x, point.get.y)).textifyBits(ls) //updating voronoi's polygon color
    }


/** test that there is no two points very near by building the set associated to the displayed points.  */
  private def ensureUniqueDisplayedPoint(): Unit = {
    case class caseVector2D(x: Int, y: Int) {}
    val big: Int = 1000000
    val setset: Set[caseVector2D] = HashSet() ++ displayedPoint.map((v: Vector2D) => caseVector2D((v.x * big).toInt, (v.y * big).toInt))
    System.out.println(setset.size + " " + displayedPoint.size)
    assert(setset.size == displayedPoint.size)
  }


  /**
   *
   * @param lociGraph  proximity relation between loci, which has been computed apriori, using a small CA
   *                   compute a neighborhood relationship between vertices, stored in the planar graph, graph..
   */
  /*def voronoiseFromGraph(lociGraph:Map[Locus,Set[Locus]]): Unit ={
   // planarGraph.reset()
    //middleClosure()
    // we will do without triangulation soon, little patience.
    computeNeighbors(lociGraph) //set the plannargraph
    voronoise(lociGraph.keySet)
  }
*/
  private def triangleSoupFromGraph(lociGraph:Map[Locus,Set[Locus]]):List[Triangle2D]={
    var triangleSoup:List[Triangle2D]=List()
     computeNeighbors(lociGraph)
    for(f<-planarGraph.faces) {
      triangleSoup=f.triangles ::: triangleSoup
    }
    triangleSoup
  }
/**
 private def triangleSoupFromQuadTree(points:Set[Vector2D])=
    {  def toFp(v:Vector2D)=FinitePoint(v.x,v.y)
      def toV2D(f:FinitePoint)=new Vector2D(f.x,f.y)
      def toTriangle2D(ppp:(FinitePoint, FinitePoint, FinitePoint))=new Triangle2D(toV2D(ppp._1),toV2D(ppp._2),toV2D(ppp._3))

      val seeds=displayedPoint.map(toFp)
      val qe: QuadEdge = Delaunay.TriangulateDelaunay(seeds,true)
      val ts: Set[(FinitePoint, FinitePoint, FinitePoint)] =qe.getTriangle()
      val triangleSoup: List[Triangle2D] =ts.map(toTriangle2D(_)).toList
      triangleSoup
      //Delaunay.TriangulateDelaunay()


    }*/
  private def triangleSoupFromDelaunay(loci: Set[Locus]) :List[Triangle2D] =  {
    var triangleSoup:List[Triangle2D]=null
    try {
      val triangulator = new DelaunayTriangulator(displayedPoint.toList.asJava)
      val t = time(triangulator.triangulate(), "triangulator.triangulate()")

       triangleSoup = triangulator.getTriangles.asScala.toList
      println(t / triangleSoup.size + "ms par triangle")
    } catch {
      case e: NotEnoughPointsException =>
    }
    triangleSoup
  }
  /**
   *
   * @param loci locus to be displayed
   *       computes the voronoi using triangle ordering, triangle middles, and border intersection   */

   def voronoise(loci: Set[Locus],lociGraph:Map[Locus,Set[Locus]]):Boolean= {
    //compute displayed points, reused by delaunayTriangle and graphTriangles.
    displayedPoint=HashSet.empty
    for (l <- loci)  displayedPoint ++= pointSet(l)
    // triangleSoupDelaunay=triangleSoupFromDelaunay(loci)
   triangleSoup=triangleSoupFromGraph(lociGraph)
     // triangleSoup=triangleSoupFromQuadTree(displayedPoint)



     val crossedEdge=planarGraph.crossingEdge() //should be empty
    // assert(crossedEdge.isEmpty,"somme edge are crossing"+crossedEdge)
    theVoronois = immutable.HashMap() ++ displayedPoint.map((v: Vector2D) => Coord2D(v.x,v.y) -> new Voroonoi(v))
    var voronoisOk=true
    for (t <- triangleSoup) {
      t.orientCCW() //triangles are oriented counter clockWise
      for (p: Vector2D <- List(t.a, t.b, t.c)) { //we collect all the triangle incident to each PE p
        val v=theVoronois(Coord2D(p.x,p.y))
         v.addTriangle(t)   //adds the delaunay triangles associated to the voronoi
    }
    }
     var polygonNotSetable=false
     for ((_, v) <- theVoronois) {
       if(v.triangles.nonEmpty)  //there can be corners, and points near corners without triangles
       try {
         v.orderTriangles()
         if(!v.trianglesOK) voronoisOk=false
         v.intersectPolygonWithBB(boundingBox)
       }
       catch {
         case _ => println("polygon not set")
           polygonNotSetable=true
       }
       /*val outsideVertice: Seq[Coord2D] =planarGraph.outerBorder.border.map(_.src)
      outsideVerticeOnBorder=outsideVertice.filter(onBorder(_))*/
       /*for ((_, v) <- voronoi) {
      v.orderTriangles()
      v.intersectPolygonWithBB(boundingBox)  //truncate the polygon so that it fits the bounding box
    }*/
     }
     !polygonNotSetable
  }

  var bug:HashSet[(Vector2D,Vector2D)]=HashSet.empty //we track V()-V() or E()-E() neighbors

  /**
   * voronoi must have been computed
   * @param loci locus which are displayed
   * @return the proximity graph between loci, a map which indicates for each locus, the set of neighbor loci
   *         does not take into account a triangle, if it intersect with the border.
   */
  def proximityLocus(loci:Set[Locus]):Map[Locus,Set[Locus]]={
    displayedPoint=HashSet.empty
    for (l <- loci)  displayedPoint ++= pointSet(l)
    //val triangleSoup=triangleSoupFromQuadTree(displayedPoint)
    val triangleSoup=triangleSoupFromDelaunay(loci)  //we use delaunay in order to find out proximity between loci
    //we build the voronoi, so as to be able to test if a triangle is on the border
    theVoronois = immutable.HashMap() ++ displayedPoint.map((v: Vector2D) => Coord2D(v.x,v.y) -> new Voroonoi(v))
    for (t <- triangleSoup) {
      t.orientCCW() //triangles are oriented counter clockWise
      for (p: Vector2D <- List(t.a, t.b, t.c)) //we collect all the triangle incident to each PE p
        theVoronois(Coord2D(p.x,p.y)).addTriangle(t)   //adds the delaunay triangles associated to the voronoi
    }
    for ((_, v) <- theVoronois) {
      v.orderTriangles()
      v.intersectPolygonWithBB(boundingBox)
    }
    val pointsOnBorder: Set[Coord2D] =theVoronois.filter(_._2.isBorder).map(_._1).toSet
    //hypothese: LocusPlanes have been computed from a previous call to middle closure, so pointSet is available
    //we record the locus of each points by building a hashmap that tells for each points, what is its locus
    val locusOfPoint:immutable.HashMap[Vector2D,Locus]=immutable.HashMap.empty++loci.map((l:Locus) => pointSet(l).toList.map((v:Vector2D)=>(v->l))).flatten
    var res:immutable.HashMap[Locus,Set[Locus]]=immutable.HashMap.empty++loci.map((l:Locus) => l->HashSet() )//initialize to empty
    /** used to determine whether reflective relation includes self pattern or/and neighbor pattern */
    var densityReflectiveDelaunay:immutable.HashMap[Locus,Int]=immutable.HashMap.empty++loci.map((l:Locus) => l->0 )//initialize to 0
    var densityReflectiveGraph:immutable.HashMap[Locus,Int]=immutable.HashMap.empty++loci.map((l:Locus) => l->0 )//initialize to 0
    /**
     *
     * @param d point
     * @param d1 other point
     *           adds a neighborhood between the loci of d and d1, except if it is a V() ,unless there is only V()
     */
    def addLocus(d: Vector2D, d1: Vector2D)= {
      if(!onSameBorder(d,d1)) { //vertice on border could be accidental linked whereas they should not
        val l = locusOfPoint(d)
        val l1 = locusOfPoint(d1)
        assert(loci.contains(l))
        val line: (Vector2D, Vector2D) = (d, d1)
        if(l==l1)
          densityReflectiveDelaunay = densityReflectiveDelaunay +  (l->(densityReflectiveDelaunay(l) + 1) )
        if ( l!=l1 ||
          l == l1 &&
            (l == V() && loci.size==1) || (l==locusE) || (l==locusF) ||  l.isTransfer)//if there is only one locus V() then there can be V-V connection
           res = res + (l -> (res(l) + l1)) //we add the proximity to d1
        else bug = bug + line
        }
      }

    bug=HashSet.empty
    for (t <- triangleSoup) {
      val triangleSummit=HashSet(t.a,t.b,t.c).map((v:Vector2D)=>Coord2D(v.x,v.y))
      if (triangleSummit.intersect(pointsOnBorder).isEmpty) //we discard triangles intersecting the border for they can bring spurious neighborhood relationship
      for ((p1,p2) <- List((t.a,t.b),(t.a,t.c),(t.c,t.b))) { //we iterate on the edges connecting two points
        addLocus(p1,p2);  addLocus(p2,p1)   }   }
    System.out.print("densityReflexiveDelaunay")
    for(l<-loci)
      System.out.print(""+l +  densityReflectiveDelaunay(l).toDouble / pointSet(locusV).size.toDouble )
    System.out.println()
   // System.out.println("loci proximity possibly causing non planarity (crossing of edges)\n"+res) //first version of the map


    //we now identify adjacency compromising planarity, and use it in order to refine our proximity graph
    middleClosure()
    computeNeighbors(res)  //compute the planargraph
    //we compute the locus of points.
    val locusOfPoint2:immutable.HashMap[Coord2D,Locus]=immutable.HashMap.empty++loci.map((l:Locus) =>pointSet(l).toList.map((v:Vector2D)=>(Coord2D(v.x,v.y)->l))).flatten
    val crossEdge=planarGraph.crossingEdge()
    val toBeCanceled: Set[(Locus, Locus)] =crossEdge.map((e:dataStruc.Edge2)=>(locusOfPoint2(e.src),locusOfPoint2(e.target)))
    //to be canceled contains pair of locus to be removed from the graph.
    //resNoCrossing refines res by removing edges between loci which cross. Those are not necessary for delaunay trianglulation because they corresponds
    // to vornoi only neighbors by a single point
    var resNoCrossing: immutable.HashMap[Locus, Set[Locus]] = new immutable.HashMap()
    for( (l:Locus,setl)<-res){
      val toRemove=toBeCanceled.filter(_._1==l).map(_._2)
      resNoCrossing=resNoCrossing + (l->setl.diff(toRemove))   //adjust res into resNoCrossing by removing the loci adjacency which caused crossingEdges
    }

     //rerun for verification
     planarGraph.resetEdgesandFaces()
    middleClosure()
    computeNeighbors(resNoCrossing)
    //compute the reflective densities, so as to compare.
    for(e<-planarGraph.edges){
      val l1=locusOfPoint2(e.src)
      val l2=locusOfPoint2(e.target)
      if(l1==l2)  densityReflectiveGraph = densityReflectiveGraph +  (l1->(densityReflectiveGraph(l1) + 1) )
    }
   if(planarGraph.suspectBigFaces.nonEmpty)
      System.out.println("big faces: "+planarGraph.suspectBigFaces)
    System.out.print("densityReflexiveGraph   ")
    for(l<-loci)
      System.out.print(""+l +  2*densityReflectiveGraph(l).toDouble / pointSet(locusV).size.toDouble )
    System.out.println()
    System.out.println("tobeCanceled"+toBeCanceled)
    System.out.println("loci proximity not causing non planarity crossing of edges"+resNoCrossing)
    resNoCrossing
  }
  /**
   * @param l a given locus on the medium.
   * @return all the point coordinate sampling l
   */
 def pointSet(l: Locus): Set[Vector2D] = {
    var res: Set[Vector2D] = Set()
    for (p <- locusPlane(l)) {
      if(p!=null)
         res ++= p.flatMap((a: Array[Option[Vector2D]]) => a.toList.flatten).toSet
    } //toList.asJava
    res
  }
}



object Medium {
  /**
   *
   * @param nbColCA   numbrt of columns
   * @param nbLineCA  number of rows.
   * @param widthLt30 width of the pannel in which we draw
   * @return builds the non toroidal hexagonal grid for the CA pannel available, assuming we know the width of the CA pannel
   */
  def christal(nbLineCA: Int, nbColCA: Int, widthLt30: Int): Medium with encodeByInt with InitSelect with border= {
    val width = if (nbColCA < 30) widthLt30 else 2 * widthLt30 //we see that for 64 column we draw the CA in the full available width by using two cells.
    val radiusSqrt = Math.floor(width.toDouble / (2 * nbColCA - 1)) //we compute radius so that the CA fills the available space on the pannel,
    // normally we assume that the number of lines is the number of columns divided by sqrt(2)
    val radius: Double = if (nbLineCA * 1.1 < nbColCA) radiusSqrt else (radiusSqrt * nbColCA) / (nbLineCA * 1.4)
    //the height should be around 1/sqrt2 the width
    assert(radius > 0, "not enough space to draw voronoi")
    //computes lattice location of points  in 2D space
    val vertices: pointLines = createPoints(nbLineCA, nbColCA)
    val deltax = 2 * radius
    val deltayTmp: Double = Math.sqrt(3) * radius
    val bb: Dimension = (
      ((nbColCA - 1) * deltax + deltax / 2).toInt,
      ((nbLineCA - 1) * deltayTmp).toInt): Dimension
    val deltay:Double= bb.height.toDouble/ (nbLineCA.toDouble-1)//faut calculer deltay de maniére a ce que ca touche la bounding box
    for (i <- 0 until nbLineCA) {
      val startx = if (i % 2 == 0) 0 else deltax / 2
      for (j <- 0 until nbColCA)
        vertices(i)(j) = Some(new Vector2D(startx + j * deltax, i * deltay))
    }
    //computation of relative neighboring relationship todo en mettre juste trois.
    val even: Array[(Int, Int)] = Array((0, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0))
    val odd: Array[(Int, Int)] = Array((0, 1), (1, 1), (1, 0), (0, -1), (-1, 0), (-1, 1))
    //defini tout, y compris comment on numérote les edge et les faces
    val neighbors: Array[Array[Array[(Int, Int)]]] = Array.ofDim[(Int, Int)](6, nbLineCA, nbColCA)
    for (i <- 0 until nbLineCA)
      for (j <- 0 until nbColCA)
        for (d <- 0 until 6)
          neighbors(d)(i)(j) =add2((i,j) , if (i % 2 == 0) even(d) else odd(d))

    //encoding and decoding differs , depending wether the number of columns is bigger than 30 or not
    if (nbColCA >= 30)new Medium(nbLineCA, nbColCA, bb, vertices, neighbors) with encodeGt with InitSelect with border{}
    else new Medium( nbLineCA, nbColCA, bb, vertices, neighbors) with encodeLt with InitSelect with border {}

  }

  /** Allocates memory for a 2D array of points */
  private def createPoints(h: Int, w: Int): pointLines = Array.ofDim[Option[Vector2D]](h, w)


  /**
   *
   * @param tuple  first tuple
   * @param tuple1 second tuple
   * @return summ of tuples
   */
  private def add2(tuple: (Int, Int), tuple1: (Int, Int)) = (tuple._1 + tuple1._1, tuple._2 + tuple1._2)


}



