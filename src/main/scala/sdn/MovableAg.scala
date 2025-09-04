package sdn

import compiler.AST.{Layer, delayed, pL}
import compiler.ASTB.True
import compiler.ASTBfun.{addRedop, orRedop, redop}
import compiler.ASTLfun.{cond, e, ltSI, neighbors, orR, reduce, uI2SIL, v}
import compiler.ASTL.{delayedL, send, transfer}
import compiler.SpatialType.{BoolE, BoolEv, BoolV, BoolVe, IntE, IntEv, IntV, IntVe, UintV, UintVx}
import compiler.{AST, ASTLfun, ASTLt, B, E, Locus, Ring, SI, T, UI, V, repr}
import compiler.repr.nomV
import dataStruc.BranchNamed
import dataStruc.DagNode.EmptyBag
import progOfmacros.Comm.neighborsSym
import progOfmacros.Wrapper.{borderS, exist, xorBin}
import sdn.{Agent, Compar, carrySysInstr}
import sdn.Util.{addLt, addSym, randUintV}
import sdntool.DistT

import scala.collection.immutable.HashMap
/** list the  movable-agent's methods which needs a processing dependant  on the locus L in V,E,Ve, F...
 * will be implemented by Vagent or VeAgent*/
trait vef[L<:Locus]{
  /** convert current value of flip, into a modification of the agent'support, in order to update next */
  def flip2next: AST[(L, B)]
  /** convert a centered move into a flip
   * invariant to check invade and empty are not simultaneously true**/
  def move2flip(m:MoveC1):BoolV
  /** convert a centered move with a possible "no component" into a flip with a possible "noflip component"
   * invariant to check yes and no are not simultaneously true*/
  def move2yesNoFlip(m:MoveC):(BoolV,Option[BoolV])
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
  override def flip2next=  delayedL( xorBin(flipAfterLocalConstr,muis) )//delayed is necessary in order to get the very last update of flip

  /** convert a move into a flip */
  override def move2flip(m:MoveC1):BoolV= {
   // val invade = exist(m.push.asInstanceOf[Sym].sym);  val empty = m.empty   //bugif empty & invade
    val invade = exist(neighborsSym(m.push));  val empty = m.empty   //bugif empty & invade


    //  val invade = exist(neighborsSym(m.push));  val empty = m.empty   //bugif empty & invade
    cond(isV,empty,invade)
  }
  override def move2yesNoFlip(m:MoveC):(BoolV,Option[BoolV])=m match{
    case m:MoveC1=> (move2flip(m),None)
    case m:MoveC2=> (move2flip(m.yes),Some(move2flip(m.no)))
  }
}


/** support location is computed from parent's support (input neighbors of the DAG */
abstract class BoundAg[L <: Locus](implicit m: repr[L]) extends  Agent[L]{
  /** describes how to computes flip from parents */
  val inheritedFlip:BoolV
  /** initial flip is computed from the parent */
  override def flipCreatedByMoves: BoolV = inheritedFlip
}
/**  code  common to Movable agents*/
abstract  class MovableAg[L <: Locus](implicit m: repr[L]) extends  Agent[L] with vef[L]
  with EmptyBag[sdn.MuStruct[_<: Locus,_<:Ring]]  {
  override val prioRand= addLt(randUintV(3)).asInstanceOf[UintVx] //si on met pas asInstance il gueule non compatibilité de override entre addLt e UintVx
  /** for the moprioment, priority is pure random.  formulation  casse gueule, car une variable a deux noms de reflection possible: prio et prioRand*/
  override val prio =prioRand //pour le moment on n'a pas encore plusieurs move possible, dans pas longtemps on va programmer prio et initalflip

  //method that depends on the spatial type of the support:


  /** Movable Agent's support is memorized in a layer a movable agent is a mustruct, to it is is called muis. */
  override val muis=new Layer[(L, B)](1, "global") with ASTLt[L,B] with Stratify [L,B] with carrySysInstr  {
    override val  next: AST[(L, B)] = flip2next.asInstanceOf[ASTLt[L,B]]   }


  /** a random priority is needed to help finalize tournament, in case of equality */
  // val prioRand = ASTLfun.concat2UI(new Rand(), new Rand()) //faudra tester
  /** les moves des movable viennent directement d'une force, et ceux des bounded ? faut voir, si ca se trouve aussi. */
  def move(force: Force) = addMoves(force.action(this), force.prio)
  /** convert centered move into one single BoolV flip */


  /** priority of the force causing the move. priority 0 is strongest
   * prio is defined for bounded agents, because it could happen they are also submitted to mutex
   * they will inherit the priority from their parents, pb if there is two parents.
   * */
  override def flipCreatedByMoves:BoolV={
    //we consider only a single move
    move2flip(moves(10).asInstanceOf[MoveC1]) //on sait qu'on a mis 9 sur repulse, todo: mettre cela d'aplomb
  }


  /** for movableAgent, canceling of flip is done by  directly voiding the agent's flip! */
  //  override def cancelFlip(where: BoolV): Unit = {  flip = flip & where  }
}



