package sdn

import compiler.ASTBfun.{addRedop, orRedop, redop}
import compiler.ASTL.{delayedL, send, transfer}
import compiler.ASTLfun.{b2SIL, f, imply, ltSI, reduce, uI2SIL, v}
import compiler.SpatialType.{BoolE, BoolEv, BoolF, BoolV, BoolVe, BoolVf, IntE, IntEv, IntV, IntVe, UintV, UintVx}
import compiler.repr.nomE
import compiler.{ASTLfun, ASTLt, B, E, F, Locus, SI, T, UI, V}
import dataStruc.{BranchNamed, Named}
import progOfCA._
import progOfmacros.Comm.{apexE, apexV}
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
   /** break symetry in case of tournament with equal priority */
  val prioRand:UintVx
   /** used for mutex tournament */
 val prio:UintVx

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
      def tmp: ASTLt[T[E, V], B] =imply(v(mutrig),ags.head.prio.lt)
    /** flip is preserved if no neighbor edge present a problem */
    def where=inside(transfer(tmp))
  }
  class MutCancelFlipIf(i: Impact,val mutex:BoolE) extends Constr(Array(this), i) {
    /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
    def mutrig:BoolE =mutex &  (impact  match {
      case Both() => insideS(currentFlip)
      case One(v) =>  insideS(currentFlip & (if (v) isV else (NisV))) // result also depend on impact
    })
    /** flip is ok if prio is minimum with respect to the other side */
    def tmp=imply(v(mutrig),prio.lt)
    def where=inside(transfer(~tmp))
  }
  /**
   *
   * @param i
   * @param mutex not more than one will flip each remote (apex) side
   */
  class MutApexKeepFlipIf(i: Impact,val mutex:BoolE) extends Constr(Array(this), i) {
    /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
    //var mutrigv:BoolE=null technique pour afficher mutrig

    def mutrig:BoolE ={
      //mutrigv=
        mutex &  (impact  match {
        case Both() => inside(apexE(f(currentFlip)))
        case One(v) =>  inside(apexE(f(currentFlip & (if (v) isV else (NisV)))))// result also depend on impact
      });
     // mutrigv.name="fliesMutrigv";      mutrigv
    }

    /** flip is ok if prio is minimum with respect to the other side */
    def tmp=imply(f(mutrig),prio.ltApex)
    def where=inside(apexV(tmp))
  }
   /**
    *
    * @param i
    * @param mutex not more than one will flip each side of mutex
    */
   class TriKeepFlipIf(i: Impact,val tritex: BoolF) extends Constr(Array(this), i) {
     /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
     def tritrig:BoolF =tritex &  (impact  match {  //y a moyen d'écrire un trigger générique pour mut,tri, et loc
       case Both() => insideS(currentFlip)
       case One(v) =>  insideS(currentFlip & (if (v) isV else (NisV))) // result also depend on impact
     })
     /** flip is ok if prio is minimum with respect to the other side */
     def tmp: BoolVf =imply(transfer(v(tritrig)),ags.head.prio.lt3)
     /** flip is preserved if no neighbor edge present a problem */
     def where=inside(tmp)
   }



   /** any agent, bounded or movable, can be constrained */
  var constrsOld: List[Constr] = List() //si je met private, ca plante. j'ai fait un catch pour récupérer inaccesible
  val constrs= new scala.collection.mutable.LinkedHashMap[String,Constr]()

   /** add c to the list of constraint */
 def constrain(name:String,c: Constr) = {
   if(constrs.contains(name))
     throw new Exception("une contrainte du nom "+name+" exite déja, changez le nom siou plait")
   constrs(name)=c
 }




  //var initialFlip:BoolV=null
  /** PEs where movements trigger changes in Agent's support. Either by filling, or by emptying
     flip is eith computed from the move for movableAgent, or  computed from the parent for bounded agent*/
  val realFlipCancel= new mutable.HashMap[String,BoolV]() with Named {}
   val rawFlipCancel= new mutable.HashMap[String,BoolV]() with Named {}

  /*
  def currentFlip: BoolV =
    flip(flip.size-1)
  def updateFlip(v:BoolV)={
    flip(flip.size)=v }
   */
  /** initial value of flip */
  val flipCreatedByMoves: BoolV

  /** priority of the force causing the move. priority 0 is strongest
   * prio is defined for bounded agents, because it could happen they are also submitted to mutex
   * they will inherit the priority from their parents, pb if there is two parents.
   * */

  var currentFlip :BoolV = null
  def refineFlip() = {
    currentFlip=flipCreatedByMoves
    for ((name, c) <- constrs) {
      rawFlipCancel(name)=c.where
      val oldFlip = currentFlip
      currentFlip = currentFlip & c.where
      realFlipCancel(name) = oldFlip & ~ currentFlip  //flip real measures the diminution in flip

    }
  }

 /* def refineFlipOld = {
    for (c <- constrsOld.reverse) {
      updateFlip(currentFlip & c.where)
    }

  }*/

  /** moves are stored in centered form, so that we can restrict them */
  var moves: HashMap[Int, MoveC] = HashMap()

  /** if move of same priority exists, signal an error */
  protected def addMoves(m: MoveC, prio: Int) = { //we may have to store set of moves, if we need add move of same priority.
    assert(!(moves.contains(prio)), "each force must have a distinct priority")
    moves(prio)=m
  }


  /** used for computing flip cancelation depending on impact */
  val isV: BoolV
   /** can be defined on agent, but needs a delayed for isV is not known yet */
  val NisV :BoolV= ~delayedL(isV)
  /** applying constraints identifies PEs where flip should be canceled, cancelFlip will implement this cancelation */
//  def cancelFlip(where: BoolV)
}
