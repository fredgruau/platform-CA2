package progOfCA

import compiler.AST.{Layer, delayed, pL}
import compiler.ASTB.True
import compiler.ASTBfun.{addRedop, orRedop, redop}
import compiler.ASTLfun.{cond, e, ltSI, neighbors, orR, reduce, uI2SIL, v}
import compiler.ASTL.{delayedL, send, transfer}
import compiler.SpatialType.{BoolE, BoolEv, BoolV, BoolVe, IntE, IntEv, IntV, IntVe}
import compiler.{AST, ASTLfun, ASTLt, B, E, Locus, Ring, SI, T, UI, V, repr}
import compiler.repr.nomV
import dataStruc.BranchNamed
import dataStruc.DagNode.EmptyBag
import progOfmacros.Comm.neighborsSym
import progOfmacros.Grad
import progOfmacros.Wrapper.{borderS, exist, xorBin}
import sdn.Agent

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
/** contains fields we often used on Vagent. Could be made lazy */
trait UtilVagent extends BranchNamed{
  self:Vagent=>
  lazy val brdE:BoolE=borderS(isV) //push everywhere possible.
  lazy val isVe:BoolVe=e(isV)
  lazy val notVe= ~isVe
  /** Ve edges leaving the support */
  lazy val brdVe=transfer(v(brdE)) & isVe
}
trait Vagent extends UtilVagent {
  self:MovableAg[V] =>
  override val isV: BoolV = is
  override val NisV=  ~isV
  //override val NisV= ~isV
  //private val _NisV= ~isV  // Champ privé  //override def NisV = _NisV

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


trait RandInt2 {
   val _rand1 = new Rand()  // Champ privé
   val _rand2 = new Rand()  // Champ privé
 val d1: ASTLt[V, UI] =ASTLfun.concat2UI (_rand1,_rand2  )      // Getter public pour le champ
  //val d1 = pL[V, UI]("dis")
  //val d: ASTLt[V, SI] =ASTLfun.uI2SIL(d1)
  val d=uI2SIL(d1)
  val dopp: IntV= -d  //rajoute un bit zero automatique pour passer de UI a SI.
  val se: IntVe = send(List(d, d, d, dopp, dopp, dopp)) //we  apply an opp on distances comming from the center.
  val grad3: IntE = reduce(addRedop[SI].asInstanceOf[redop[SI]], transfer(se)) //the trick here is to do the expensive operation (add) only on the three edges locus, instead of the 6 Ve transfer
  val grad6: IntEv = send(List(-grad3, grad3))
  val slopEv: BoolEv = ltSI(grad6) //when sending back the result to EV, we have to invert again towards the center
  // val slop: BoolVe = cond(chip.borderVe.df, transfer(slopEv), false) //faut definir ckispasse au bord. we put zero if unedfined
  val sloplt=transfer(slopEv)
  val level: BoolE = ~reduce(orRedop[B], slopEv) //its equal if it is neither lt nor gt


  //val (sloplt: BoolVe,  level) = Grad.slope(randInt)
}


/**  code  common to Movable agents*/
abstract  class MovableAg[L <: Locus](implicit m: repr[L]) extends  Agent[L] with EmptyBag[MuStruct[_<: Locus,_<:Ring]]  {


  def flip2next: AST[(L, B)]
  /** convert a centered move into a flip
   * invariant to check invade and empty are not simultaneously true**/
  def move2flip(m:MoveC1):BoolV
  /** convert a centered move with a possible "no component" into a flip with a possible "noflip component"
   * invariant to check yes and no are not simultaneously true*/
  def move2yesNoFlip(m:MoveC):(BoolV,Option[BoolV])

  /** Movable Agent's support is memorized in a layer. */
  override val is=new Layer[(L, B)](1, "global") with ASTLt[L,B] with carrySysInstr {
    override val  next: AST[(L, B)] = flip2next   }


  /** a random priority is needed to help finalize tournament, in case of equality */
  // val prioRand = ASTLfun.concat2UI(new Rand(), new Rand()) //faudra tester
    /** les moves des movable viennent directement d'une force, ceux des bounded ? faut voir, si ca se trouve aussi. */
  def move(force: Force) = addMoves(force.action(this), force.prio)
  /** convert centered move into one single BoolV flip */

  override def setFlip:BoolV={
    //we consider only a single move
    move2flip(moves(10).asInstanceOf[MoveC1])
  }


  /** for movableAgent, canceling of flip is done by  directly voiding the agent's flip! */
//  override def cancelFlip(where: BoolV): Unit = {  flip = flip & where  }
}



