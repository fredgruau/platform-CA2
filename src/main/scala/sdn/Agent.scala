package sdn

import compiledMacro.compute
import compiler.ASTL.delayedL
import compiler.SpatialType.BoolV
import compiler.{B, Locus}
import dataStruc.{BranchNamed, Named}
import progOfCA._
import progOfmacros.Compute

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
abstract class Agent[L <: Locus] extends MuStruct[L, B] {

  /**
   *
   * @param ags one or two agents on which to apply constraint
   *            constraints are inner classes of agents, so that they can access is.
   */

  abstract class Constr2(val ags: Array[Agent[_ <: Locus]], val impact: Impact) {
    /** where = places where flips is still valid after constraint has been applied*/
    def where: BoolV //will use fields from the agent: flip, as well as this

    def whereImpact: BoolV
  }

  /**
   *
   * @param i     wether if is both, or one(bool)
   */
  abstract class LocCtrKeepFlipIf(i: Impact) extends Constr2(Array(this), i) {
    /** the constraint will impose flip to occur at where, it may also depend on impact */
    override def whereImpact: BoolV = impact match {
      case Both() => where
      case One(v) =>  Compute.imply (if (v) isV else (NisV),where)
    }
  }
  abstract class LocCtrCancelFlipIf(i: Impact) extends Constr2(Array(this), i) {
    /** the constraint will impose flip to occur at where, it may also depend on impact */
    override def whereImpact: BoolV = impact match {
      case Both() => ~where
      case One(v) =>  Compute.imply (if (v) isV else (NisV),~where)
    }

  }

  /** any agent, bounded or movable, can be constrained */
  var constrs: List[Constr2] = List() //si je met private, ca plante. j'ai fait un catch pour récupérer inaccesible

  /** add c to the list of constraint */
  def constrain(c: Constr2) = {
    constrs = c :: constrs
  }


  /** flip computed from the move of the parents */
  //var initialFlip:BoolV=null
  /** PEs where movements trigger changes in Agent's support. Either by filling, or by emptying */
  //var flip: BoolV = null
  val flip= new mutable.HashMap[Int,BoolV]() with Named with BranchNamed {}

  //var flip2:HashMap[Int,BoolV]=HashMap()
  def currentFlip: BoolV =flip(flip.size-1)
  def updateFlip(v:BoolV)={
    flip(flip.size)=v }
  /** initial value of flip */
  def setFlip: BoolV

  def refineFlip = {
    for (c <- constrs.reverse) {
      updateFlip(currentFlip & c.whereImpact)
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
