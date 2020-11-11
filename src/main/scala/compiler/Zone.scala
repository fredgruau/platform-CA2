package compiler

/**Represents a Connected component of affectations either of spatial type transfer (<:TT) or E,V,T, whose schedule are aligned:
 * the spatial mu component are evaluated one after the   other for all the instructions */

import compiler.Constraint.Partition
import compiler.Circuit._
import dataStruc.{Edge, Graph, Named, Vertex}
import compiler.Instr.a
import scala.collection._

/** A zoneV is a connected component of instructions which are aligned, and therefore scheduled together */
abstract class ZoneV  extends Vertex[ZoneV,EdgeZ] {
  /** root of the tree used during the union find algorithm to compute connected component of instructions*/
  def root: Instr
  /** Locus of root */
  def locus =root.locus.get
  /** name of variable set by root instruction*/
  override def name:String =a(root).name
  /** Constraint for folding. it is progressively refined, until it includes only one single schedule to be followed */
  var foldConstr: Constraint=_;
  /** true is the several scalar registers encoding the locus can coalesc into a single register */
  var folded:Boolean = false;
  /** true for transfer zone */
  def isTransfer=locus.isTransfer
  /** prints the name, the locus, whether it is folded, the current constraints, and the edges */
  override def toString: String = " Node " + name +" "+ (  if(!folded) "not"else "")+"folded"+
    " constr:  "+ foldConstr +" IN-edges: [" + inNeighbors.map( _.toString) + "]" +" OUT-edges: [" + outNeighbors.map( _.toString) + "]"

  /**
   * @param nodes nodes that should be revisited
   * resets visited on nodes and edges
   */
  def resetVisited(nodes:List[ZoneV])=
    for(n<-nodes){
      n.visited=false
      for(e<-n.inNeighbors)
        e.visited=false
    }
  /**
   * for non-vertex SCC,
 * Intersect neighbor TCC's constraint with  partition constraint, input AND OUTPUT neighbors.
   *  propagate the neighbor TCC's constraint through the partition, to the SCC
   */
  def setFoldConstrSimplicial():Unit=
    if ( locus==V()) folded=false //we do not want to consider simplicial zone as folded, there is nothing to fold
    else if( isTransfer ) folded = !foldConstr.empty
    else {
      //  new constraints for neighboring transfer zones,
    val updtConstrs=neighborsEV .map((ev:(EdgeZ,ZoneV))=>ev._1.partition.get.intersect(ev._2.foldConstr) )
      if(!updtConstrs.map(_.empty).reduce((x, y) => x || y)) {  // if none of those are empty
        //we propagate the updated constraint Cev._2   using  the  partitions.Cev._1._1.partition
        val  propagatedConstrs=(neighborsEV.zip(updtConstrs) ).map(Cev=>Constraint.propagate( Cev._1._1.partition.get,Cev._2 ) )
        //and then do the interesection.
        val newConstr=Constraint.intersect(foldConstr::propagatedConstrs, locus )
        // if SCC is foldable, we update with the new computed constraints
        if(!foldConstr.empty) {
          foldConstr=newConstr;
          (neighborsV.zip(updtConstrs)).map( (nc:(ZoneV,Constraint))=>nc._1.foldConstr= nc._2)
          folded=true
        }
        else folded = false
      }
      else folded=false
    }
  /** For folded node,
   * all the input neighbors of "this" which are folded have already applied pick, and have a single schedule
   * we propagate those single schedule using the partition constraint, and intersect with the current constraint.
   * if the resulting constraint is not empty, we set folded to true
   * and also pick a single schedule in this resulting constraint.
   * otherwise we leave the constraint unchanged
   *  */
  def pick() =   if(folded){
    //we consider only folded neighbors.
   val foldedInNeighbors= inNeighbors.filter(_.in.folded)
    val propagateConstr=foldedInNeighbors.map((e:EdgeZ)=>Constraint.propagate(e.partition.get,e.in.foldConstr))
   val newConstr=Constraint.intersect(foldConstr::propagateConstr,foldConstr.locus)
    if( newConstr.empty) folded=false
    else  foldConstr =newConstr.pick()
  }
}


/**  Edge linking two zones  */
abstract class EdgeZ extends Edge[ZoneV,EdgeZ]{
  /** one of {in , out} is a  SCC, the other is a TCC, the  partition constraint on the TCC must be checked for the SCC to be foldable
   * It also is used to propagate constraints,
   * edges linking to an Scc of type vertex are not supressed, so that there is not allways a partition */
  def partition: Option[Partition]
  /** used to visit all edges*/
  override def toString: String= in.name + "->" + out.name +":"+ partition
  def propagate={
    // if()
  }
}

object ZoneV{
  /**
   * @param instrs
   * @param zones mutable hash tablet
   * @param c possible cycle-constraints computed during alignment
   * @return a zone of aligned instructions.
   */
  def apply(instrs:Iterable[Instr], zones:    TabSymb[ZoneV ],   c:TabSymb[Constraint]): ZoneV = {
    /** @param i input Instruction
     * @ return i's constraint aligned on the root if there is one, otherwise none  */
    def alignedConstr(i:Instr ):Option[Constraint]= { val n=a(i).name
      if(c.contains(n)) Some(c(n).permute(i.alignToRoot,i.root.locus.get))  else None }
    new ZoneV  {
      val root=instrs.head.root
      foldConstr =if(isTransfer) Constraint.intersect( instrs.flatMap( alignedConstr(_)).toList ,locus)
      else Constraint.AllConstr(locus)  //ya pas de contraintes générées sur les zones simpliciales
       val inNeighbors: List[EdgeZ] = {
        val instrIntputInstr: Iterable[(Instr, Instr)] = instrs.flatMap((i: Instr) =>
          i.inputNeighbors.filter( (i2:Instr) =>  i2.root != root ).map((i, _)) ) //we consider inputNeigbors in a distinct zone
        instrIntputInstr.map( (i:Tuple2[Instr,Instr]) => EdgeZ(i._1,i._2,zones )) //zones is used here
                                                              .toSet.toList //removes possible doublons
        }

    }
  }

}


object EdgeZ{
  /** @param i output instruction
   *  @param i2 instruction producing a variable used by i
   * Build a  edge from  a zone containing, iinput to a zone containing i.  */
  def apply(i:Instr, i2:Instr, zones:TabSymb[ZoneV ]):EdgeZ={
    require(i.isTransfer ^ i2.isTransfer)
    val iloc=i.locus.get;val i2loc=i2.locus.get
    val partPerm = if(iloc==V() || i2loc==V())  None //throw new RuntimeException("no partition towards V" + i + i2 )
    else    Some (if(i.isTransfer) //$i2 is simplicial
    {  val partition: Constraint = Partition (i.alignPerm(a(i2).name), i2.locus.get.asInstanceOf[S],i.locus.get.asInstanceOf[TT]) //constraint on i 's schedule
        partition.permute(i.alignToRoot,i.root.locus.get).asInstanceOf[Partition] } //expressed with respect to the root.
    else { // $i is simplicial, $i2 is transfer
        val slocus=iloc.asInstanceOf[S]
        val partition = Partition(slocus.proj, slocus, i2.locus.get.asInstanceOf[TT]) //when doing a reduction,
                                                              // the mapping from Tlocus to Slocus is constant, and determined by the slocus
        partition.permute(i2.alignToRoot, i2.root.locus.get)  //align on root
        })

    new EdgeZ{lazy val in=zones(a(i2.root).name);lazy val out =zones(a(i.root).name); val partition=partPerm }

  }
}


