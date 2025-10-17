package sdn

import compiler.SpatialType.{BoolV, UintV}
import compiler.{AST, B, Locus, Ring, V, repr}
import dataStruc.DagNode
import dataStruc.DagNode.Singleton
import sdntool.addDist

/**
 * support location is partially computed from parent's support (input neighbors of the DAG )
 * @param follows Move that is imposed to the agent so that its follows the bounding agent
 * @param arg input agents which is bounding */
abstract class BoundedAgV(init:String, arg: MuStruct[_<:Locus,_ <:Ring] , val follows:Force ) extends  MovableAg[V](init) with  MovableAgV  with dataStruc.DagNode.Singleton[sdn.MuStruct[_ <: compiler.Locus, _ <: compiler.Ring]]

/** to be used later on, when we implement simult */
class Voronoi (parent: MuStruct[V,B] with addDist with addGcenter) extends BoundedAgV("globalInv",parent.d, parent.gc.keepInside) {
  override def arg = parent

}