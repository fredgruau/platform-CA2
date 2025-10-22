package sdn

import compiler.SpatialType.{BoolV, BoolVe, UintV}
import compiler.{AST, B, Locus, Ring, V, repr}
import dataStruc.DagNode
import dataStruc.DagNode.Singleton
import progOfStaticAgent.{Homogen, HomogeneizeCA}
import sdntool.addDist



/** voronoi is our first instance of bounded agents, so we define it here. */
class Vor(h:MovableAgV with addDist with addGcenter) extends MovableAg[V]("globalInv") with MovableAgV with addBloobV with blobConstrain with blobConstrTrou
{  override def inputNeighbors=List(h.gc,h.d)
  /** exploring priority */
  var tmp:BoolV=null; var tmp2:BoolV=null; var tmpVe:BoolVe=null;
  //val explore=introduceNewPriority();  force(explore, "explore",'O', bf.smoothen)
  val homogeneize=introduceNewPriority()
  force(homogeneize,"repulse",'|',h.d.repulseVor)//specific forces applied to Flies
  val containsGcenter=introduceNewPriority()
  force(containsGcenter,"containGcenter",'>',h.gc.keepInside) //todo, this is a forced move to be supplied directly upon definition of bounded agent
  shoowText(h.d.muis, List())
}

trait addVor {
  self:MovableAgV with addDist  with addGcenter=>
  val vor=new Vor(this)
}
/**
 * support location is partially computed from parent's support (input neighbors of the DAG )
 * @param follows Move that is imposed to the agent so that its follows the bounding agent
 * @param arg input agents which is bounding */
abstract class BoundedAgV(init:String, arg: MuStruct[_<:Locus,_ <:Ring] , val follows:Force ) extends  MovableAg[V](init) with  MovableAgV  with dataStruc.DagNode.Singleton[sdn.MuStruct[_ <: compiler.Locus, _ <: compiler.Ring]]

/** to be used later on, when we implement simult */
class Voronoi (parent: MuStruct[V,B] with addDist with addGcenter) extends BoundedAgV("globalInv",parent.d, parent.gc.keepInside) {
  override def arg = parent

}