package progOfCA

import compiler.AST.{Layer, delayed, pL}
import compiler.ASTB.True
import compiler.ASTBfun.{addRedop, orRedop, redop}
import compiler.ASTLfun.{cond, e, ltSI, neighbors, orR, reduce, uI2SIL, v}
import compiler.ASTL.{delayedL, send, transfer}
import compiler.SpatialType.{BoolE, BoolEv, BoolV, BoolVe, IntE, IntEv, IntV, IntVe, UintV}
import compiler.{AST, ASTLfun, ASTLt, B, E, Locus, Ring, SI, T, UI, V, repr}
import compiler.repr.nomV
import dataStruc.BranchNamed
import dataStruc.DagNode.EmptyBag
import progOfmacros.Comm.neighborsSym
import progOfmacros.Wrapper.{borderS, exist, xorBin}
import sdn.{Agent, Compar}
import sdn.Util.{addLt, randUintV}

import scala.collection.immutable.HashMap
/** all the agent's methods which needs a processing dependant  on the locus L in V,E,Ve, F...
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
/** contains fields we often use on Vagent. Could be made lazy */
trait UtilVagent extends BranchNamed{
  self:Vagent=>
  lazy val brdE:BoolE=borderS(isV) //push everywhere possible.
  lazy val isVe:BoolVe=e(isV)
  lazy val notVe= ~isVe
  /** Ve edges leaving the support */
  lazy val brdVe=transfer(v(brdE)) & isVe
}

trait Vagent extends vef[V] with UtilVagent {
  self:MovableAg[V] =>
  override val isV: BoolV = is
  //override val NisV=  ~isV
  override def flip2next=  delayedL( xorBin(currentFlip,is) )//delayed is necessary in order to get the very last update of flip
  override def move2flip(m:MoveC1):BoolV= {
    val invade = exist(neighborsSym(m.push));  val empty = m.empty   //bugif empty & invade
    cond(isV,empty,invade)
  }
  override def move2yesNoFlip(m:MoveC):(BoolV,Option[BoolV])=m match{
    case m:MoveC1=> (move2flip(m),None)
    case m:MoveC2=> (move2flip(m.yes),Some(move2flip(m.no)))
  }
}


/** support location is computed from parent's support (input neighbors of the DAG */
abstract class BoundAg[L <: Locus](implicit m: repr[L]) extends  Agent[L]{
  val inheritedFlip:BoolV
  /** initial flip is computed from the parent */
  override val initialFlip: BoolV = inheritedFlip
}
/**  code  common to Movable agents*/
abstract  class MovableAg[L <: Locus](implicit m: repr[L]) extends  Agent[L] with vef[L] with EmptyBag[MuStruct[_<: Locus,_<:Ring]]  {
  override val prioRand= addLt(randUintV(5))
  /** for the moment, priority is pure random */
 override val prio =prioRand //pour le moment on n'a pas encore plusieurs move possible, dans pas longtemps on va programmer prio et initalflip
//method that depends on the spatial type of the support:


  /** Movable Agent's support is memorized in a layer. */
  override val is=new Layer[(L, B)](1, "global") with ASTLt[L,B] with carrySysInstr {
    override val  next: AST[(L, B)] = flip2next   }


  /** a random priority is needed to help finalize tournament, in case of equality */
  // val prioRand = ASTLfun.concat2UI(new Rand(), new Rand()) //faudra tester
    /** les moves des movable viennent directement d'une force, ceux des bounded ? faut voir, si ca se trouve aussi. */
  def move(force: Force) = addMoves(force.action(this), force.prio)
  /** convert centered move into one single BoolV flip */


  override lazy val initialFlip:BoolV={
    //we consider only a single move
    move2flip(moves(10).asInstanceOf[MoveC1])
  }


  /** for movableAgent, canceling of flip is done by  directly voiding the agent's flip! */
//  override def cancelFlip(where: BoolV): Unit = {  flip = flip & where  }
}



