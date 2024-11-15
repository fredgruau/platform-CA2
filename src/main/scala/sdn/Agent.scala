package sdn

import compiler.ASTBfun.{addRedop, orRedop, redop}
import compiler.ASTL.{delayedL, send, transfer}
import compiler.ASTLfun.{b2SIL, imply, ltSI, reduce, uI2SIL, v}
import compiler.SpatialType.{BoolE, BoolEv, BoolV, BoolVe, IntE, IntEv, IntV, IntVe, UintV}
import compiler.repr.nomE
import compiler.{ASTLfun, ASTLt, B, Locus, SI, UI, V}
import dataStruc.{BranchNamed, Named}
import progOfCA._
import progOfmacros.{Compute, Grad}
import progOfmacros.Compute.implique
import progOfmacros.Wrapper.{exist, inside, insideS}


import scala.collection.convert.ImplicitConversions.`map AsJavaMap`
import scala.collection.mutable.HashMap
import scala.collection.mutable
/** makes precise where the constraint applies*/
sealed trait Impact
/** constraint is applied whether it is empty or not */
case class Both() extends Impact
/**  constraint will prevent filling (resp emptying), if noFill is true (resp. false)*/
case class One(noFill: Boolean) extends Impact //on veut pouvoir calculer le complementaire d'une contraint, forbid et oblige sont complementaire


/** agents are boolean muStruct */
abstract class Agent[L <: Locus] extends MuStruct[L, B]
 {
  /** for the moment, priority is pure random */
  val prioRand:UintV
 val prio:UintV

  /** used for mutex tournament */
//  val prioLt: BoolEv= Grad.lt(uI2SIL(prio))
   val (  prioLt, level)=Grad.slopeLt(uI2SIL(delayedL( prioRand)))
  /**
   *
   * @param ags one or two agents on which to apply constraint
   *            constraints are inner classes of agents, so that they can access is.
   */

  abstract class Constr(val ags: Array[Agent[_ <: Locus]], val impact: Impact) {
    /** where = places where flips is still valid after the constraint newFlip<-olcFlip&where
     * defined has a method, in order allow definition prior to intanciation of needed field, such as flip.*/
    def where: BoolV //will use fields from the agent: flip, as well as this
  }

class KeepFlipIf(i: Impact,val loc:BoolV) extends Constr(Array(this), i)
  { override def where: BoolV = impact match {
      case Both() => loc
      case One(v) =>  implique (if (v) isV else (NisV),loc)
    }
  }
  /** Same as KeepFlipIf, exept that now, loc is a method, so that the constraint can be
   * defined at a moment where loc is not known*/
  abstract class KeepFlipIfWithDef(i: Impact) extends Constr(Array(this), i)
  { def loc:BoolV
    override def where: BoolV = impact match {
      case Both() => loc
      case One(v) =>  implique (if (v) isV else (NisV),loc)
    }
  }
  class CancelFlipIf(i: Impact, l:BoolV) extends KeepFlipIf(i,~l)

  /**
   *
   * @param i
   * @param mutex not more than one will flip each side of mutex
   */
  class MutKeepFlipIf(i: Impact,val mutex:BoolE) extends Constr(Array(this), i) {
    /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
    def mutrig:BoolE =mutex &  (impact  match {
      case Both() => insideS(currentFlip)
      case One(v) =>  insideS(currentFlip & (if (v) isV else (NisV))) // result also depend on impact
    })
    /** flip is ok if prio is minimum with respect to the other side */
      def tmp=imply(v(mutrig),ags.head.prioLt)
    def where=inside(transfer(tmp))
  }
  class MutCancelFlipIf(i: Impact,val mutex:BoolE) extends Constr(Array(this), i) {
    /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
    def mutrig:BoolE =mutex &  (impact  match {
      case Both() => insideS(currentFlip)
      case One(v) =>  insideS(currentFlip & (if (v) isV else (NisV))) // result also depend on impact
    })
    /** flip is ok if prio is minimum with respect to the other side */
    def tmp=imply(v(mutrig),prioLt)
    def where=inside(transfer(~tmp))
  }
  /**
   *
   * @param i
   * @param mutex not more than one will flip each remote (apex) side
   */
  class MutApexKeepFlipIf(i: Impact,val mutex:BoolE) extends Constr(Array(this), i) {
    /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
    def mutrig:BoolE =mutex &  (impact  match {
      case Both() => insideS(currentFlip)
      case One(v) =>  insideS(currentFlip & (if (v) isV else (NisV))) // result also depend on impact
    })
    /** flip is ok if prio is minimum with respect to the other side */
    def tmp=imply(v(mutrig),prioLt)
    def where=inside(transfer(tmp))
  }
  /** any agent, bounded or movable, can be constrained */
  var constrs: List[Constr] = List() //si je met private, ca plante. j'ai fait un catch pour récupérer inaccesible

  /** add c to the list of constraint */
  def constrain(c: Constr) = {
    constrs = c :: constrs
  }



  //var initialFlip:BoolV=null
  /** PEs where movements trigger changes in Agent's support. Either by filling, or by emptying
     flip is eith computed from the move for movableAgent, or  computed from the parent for bounded agent*/
  val flip= new mutable.HashMap[Int,BoolV]() with Named {}

  //var flip2:HashMap[Int,BoolV]=HashMap()
  def currentFlip: BoolV =
    flip(flip.size-1)
  def updateFlip(v:BoolV)={
    flip(flip.size)=v }
  /** initial value of flip */
  val initialFlip: BoolV

  /** priority of the force causing the move. priority 0 is strongest
   * prio is defined for bounded agents, because it could happen they are also submitted to mutex
   * they will inherit the priority from their parents, pb if there is two parents.
   * */


  def refineFlip = {
    for (c <- constrs.reverse) {
      updateFlip(currentFlip & c.where)
    }

  }

  /** moves are stored in centered form, so that we can restrict them */
  var moves: HashMap[Int, MoveC] = HashMap()

  /** if move of same priority exists, signal an error */
  protected def addMoves(m: MoveC, prio: Int) = { //we may have to store set of moves, if we need add move of same priority.
    assert(!(moves.contains(prio)), "each force must have a distinct priority")
    moves(prio)=m
  }


  /** used to compute flip cancelation depending on impact */
  val isV: BoolV
  val NisV :BoolV
  /** applying constraints identifies PEs where flip should be canceled, cancelFlip will implement this cancelation */
//  def cancelFlip(where: BoolV)
}
