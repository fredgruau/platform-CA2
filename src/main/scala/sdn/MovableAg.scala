package sdn

import compiler.AST.{Layer, delayed, pL}
import compiler.ASTB.True
import compiler.ASTBfun.{addRedop, derivative, orRedop, redop, unaryToBinary2}
import compiler.ASTLfun.{cond, e, ltSI, neighbors, neq, orR, orScanRight, reduce, uI2SIL, v}
import compiler.ASTL.{delayedL, send, transfer, unop}
import compiler.SpatialType.{BoolE, BoolEv, BoolV, BoolVe, IntE, IntEv, IntV, IntVe, UintV, UintVx}
import compiler.{AST, ASTLfun, ASTLt, B, E, Locus, Ring, SI, T, UI, V, repr}
import compiler.repr.nomV
import dataStruc.BranchNamed
import dataStruc.DagNode.EmptyBag
import progOfmacros.Comm.neighborsSym
import progOfmacros.Wrapper.{borderS, exist, unary2Bin, xorBin}
import sdn.{Agent, Compar, carrySysInstr}
import sdn.Util.{addLt, addSym, randUintV}
import sdntool.DistT

import scala.collection.immutable.HashMap
/** list the  movable-agent's methods which needs a processing dependant  on the locus L in V,E,Ve, F...
 * will be implemented by Vagent or VeAgent*/
trait vef[L<:Locus]{
  /**  computes the new agent'support from flip.
   * for V agent it is a simple xor,
   * for Ve agents there will be a non trivial computation */
  def flip2next: AST[(L, B)]
}
/** contains fields we often use on Vagent.  made lazy because possibly not used */
trait UtilVagent extends BranchNamed{
  self:MovableAgentV=>
  lazy   val brdE:BoolE=borderS(isV) //push everywhere possible.
  lazy val isVe:BoolVe=e(isV)
  lazy val notVe= ~isVe
  /** Ve edges leaving the support , we know we may take a sym so we prepare for it, to get a meaningfull name brdVe.sym*/
  lazy val brdVe=addSym( transfer(v(brdE)) & isVe)
}

/** defines the methods in vef[V], adds UtilVagent, which mixin some further usefull field*/
trait MovableAgentV extends MovableAg[V] with vef[V] with UtilVagent {
  self:MovableAg[V] =>
  override val isV: BoolV = muis
  //override val NisV=  ~isV
  override def flip2next=  delayedL( xorBin(flipRandomlyCanceled,muis) )//delayed is necessary in order to get the very last update of flip

}


/**  code  common to Movable agents which stores a support
 * and can directly apply the move on this support in order to modify it */
abstract  class MovableAg[L <: Locus](implicit m: repr[L]) extends  Agent[L] with vef[L]
  with EmptyBag[sdn.MuStruct[_<: Locus,_<:Ring]]  {

  override def allTriggered:UintV={
    moves.map(_.values.map(_.triggered).reduce(_ | _).asInstanceOf[UintV]).toList.reduce(_ :: _)
  }
  override def allTriggeredYes:UintV={
    moves.map(_.values.map(_.triggeredYes).reduce(_ | _).asInstanceOf[UintV]).toList.reduce(_ :: _)
  }
  override def  allFlip: UintV ={
    moves.map(_.values.map(_.move2flip(isV)).reduce(_ | _).asInstanceOf[UintV]).toList.reduce(_ :: _)
  }


/*

  var tmp:(UintVx,BoolV)=null
  override def flipAndPrioCreatedByMoves:(UintV,BoolV,UintV)={
    /** todo: when reducing with |, we must verify that a single move is triggered, among those of equal priority */
    val triggered: UintV =moves.map(_.values.map(_.triggered).reduce(_ | _).asInstanceOf[UintV]).toList.reduce(_ :: _)
    val filledTriggered=orScanRight(triggered)
    /** all false except for highest priority move*/
    val highgestTriggered=unop(derivative, filledTriggered)
    /** flips for all priorities */
    val allFlip: UintV =moves.map(_.values.map(_.move2flip(isV)).reduce(_ | _).asInstanceOf[UintV]).toArray.reduce(_ :: _)
    /** selectionne le flip parmis les flip des mouvement proposés */
    ( unary2Bin(filledTriggered ),neq(highgestTriggered&allFlip),highgestTriggered)
    //we consider only a single move
    //move2flip(moves(10).asInstanceOf[MoveC1]) //on sait qu'on a mis 9 sur repulse, todo: mettre cela d'aplomb
  }
*/

  /** a random priority is needed to help finalize tournament, in case of equality */
  override val prioRand= {
    /** c'est plus sérieux avec deux bits de random priority */
    val x=randUintV(2)
    (x ).asInstanceOf[UintV]
  } //sans "asInstance" il gueule non compatibilité de override entre addLt e UintVx

  /** Movable Agent's support. It is memorized in a layer a movable agent is a mustruct, so it is  called muis. */
  override val muis=new Layer[(L, B)](1, "global") with ASTLt[L,B] with Stratify [L,B] with carrySysInstr  {
    override val  next: AST[(L, B)] = flip2next.asInstanceOf[ASTLt[L,B]]   }

  /** les moves des movable viennent directement d'une force, et ceux des bounded ? faut voir, si ca se trouve aussi. */
  def force(priority:Int, name:String,shortName:Char, force: Force) = {
    addMoves(priority, name, shortName, force.action(this))
  }

  /** for the moment, priority is pure random.  formulation  casse gueule,
   * car une variable a deux noms de reflection possible: prio et prioRand
   * priority of the force causing the move. priority 0 is weakest
   * prio is defined for bounded agents, because it could happen they are also submitted to mutex
   *  they will inherit the priority from their parents, pb if there is two parents.
   */
  //override val prio =prioRand //pour le moment on n'a pas encore plusieurs move possible, dans pas longtemps on va programmer prio et initalflip


  /** for movableAgent, canceling of flip is done by  directly voiding the agent's flip! */
  //  override def cancelFlip(where: BoolV): Unit = {  flip = flip & where  }
}



/** support location is computed from parent's support (input neighbors of the DAG */
abstract class BoundAg[L <: Locus](implicit m: repr[L]) extends  Agent[L]{
  /** describes how to computes flip from parents */
  val inheritedFlip:BoolV
  /** initial flip is computed from the parent */
  override def allTriggered:UintV=null;
  override def allTriggeredYes:UintV=null
 // override def flipAndPrioCreatedByMoves: (UintVx,BoolV,UintV) = (null,inheritedFlip,null)
}

