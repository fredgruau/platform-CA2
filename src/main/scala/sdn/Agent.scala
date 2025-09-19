package sdn

import compiler.ASTB.{False, Uint}
import compiler.ASTBfun.{addRedop, derivative, ltUI2, orRedop, redop}
import compiler.ASTL.{delayedL, send, transfer, unop}
import compiler.ASTLfun.{allOne, andLB2R, b2SIL, eq0, f, imply, lt2, ltSI, neq, orScanRight, reduce, uI2SIL, v}
import compiler.SpatialType.{BoolE, BoolEv, BoolF, BoolV, BoolVe, BoolVf, IntE, IntEv, IntV, IntVe, UintV, UintVx}
import compiler.repr.nomE
import compiler.{ASTLfun, ASTLt, B, E, F, Locus, SI, T, UI, V}
import dataStruc.{BranchNamed, Named}
import progOfCA._
import progOfmacros.Comm.{apexE, apexV}
import progOfmacros.{Compute, Grad}
import progOfmacros.Compute.implique
import progOfmacros.Wrapper.{exist, inside, insideS, not, unary2Bin}
import sdn.Globals.root4naming
import sdn.Util.addLt

import scala.::
import scala.Predef._
import scala.collection.convert.ImplicitConversions.`map AsJavaMap`
import scala.collection.mutable.{ArrayBuffer, HashMap}
import scala.collection.mutable
/** makes precise where a constraint applies*/
sealed trait Impact
/** constraint is applied whether it is empty or not */
case class Both() extends Impact
/**  constraint will prevent filling (resp emptying), if noFill is true (resp. false)*/
case class One(noFill: Boolean) extends Impact //on veut pouvoir calculer le complementaire d'une contraint, forbid et oblige sont complementaire


/** agents are boolean muStruct */
abstract class Agent[L <: Locus] extends MuStruct[L, B]
 {

/** the agent's list of consrtrain. Constraints have a name, and the list is also ordered */
   val constrs= new scala.collection.mutable.LinkedHashMap[String,Constr]()
   def codeConstraint: Iterable[String] =constrs.keys.toList.map(_.charAt(0).toString)
   def showConstraint={ shoowText(allFlipCancel,codeConstraint.toList)}
   def codeMove:Iterable[String] =
     moves.map(_.keys.head.charAt(0).toString)
   def showMoves={ shoowText(highestTriggered,codeMove.toList)}
   def showPositiveMoves={ shoowText(highestTriggeredYes,codeMove.toList)}

   /**
    *
    * @param name more explicit name
    * @param shortName used for display in CApannel
    * @param c constraint
    */

 def constrain(name:String, shortName:Char, c: Constr) = {
   if(constrs.contains(shortName+name))
     throw new Exception("une contrainte du nom "+name+" exite déja, changez le nom siou plait")
   constrs(shortName+name)=c
 }


   /** moves are stored in centered form, so that we can restrict them we store one hashmap for each priority. It two moves with identical names are added, we'd have to merge those */
   val moves:ArrayBuffer[mutable.LinkedHashMap[String,MoveC]] = ArrayBuffer() //empty at the beginning
   /** we introdued a new priority use to qualify a new range of move, creating a new functionnality such  as explore, homogeneize, stabilize*/
   def introduceNewPriority():Int={ moves+= mutable.LinkedHashMap[String,MoveC]();  moves.size-1 }
   /** if move of same priority exists, signal an error */
   protected def addMoves(priority:Int, name:String, shortName:Char, m: MoveC ) = { //we may have to store set of moves, if we need add move of same priority.
     val ht=moves(priority)
     assert(!(ht.contains(name)), "each force must have a distinct priority");
     moves(priority)(shortName+name)=m
   }

   def allTriggered:UintV
   def allTriggeredYes:UintV
   val filledTriggered=orScanRight(delayedL(allTriggered))
   val filledTriggeredYes=orScanRight(delayedL(allTriggeredYes))
   /** all false except for highest priority move*/
   val highestTriggered=unop(derivative, filledTriggered)
   val highestTriggeredYes=unop(derivative, filledTriggeredYes)
   /** flips for all priorities */
   def allFlip:UintV
    /** selectionne le flip parmis les flip des mouvement proposés */
    val flipOfMove=neq(highestTriggered&delayedL( allFlip))
   val prioDet=unary2Bin(filledTriggered )
   val prioDetYes=unary2Bin(filledTriggeredYes )
   /** selected positive move has lower priority than selected move, */
   val isQuiescent:BoolV =lt2(prioDetYes,prioDet)

   /** random integer used for breaking  symetry in case of tournament with equal priority */
   val prioRand:UintV
    val prio: UintVx =addLt(prioRand::prioDet)
   val prioYes: UintVx =addLt(prioRand::prioDetYes)
   /** nullify prio if quiescent */
   val prioYesNotQuiescent=andLB2R(~ isQuiescent, prioYes)



   /*
      /** initial value of flip cause by movements for movable agents, or inherited for bound agents*/
     def flipAndPrioCreatedByMoves: (UintV,BoolV,UintV)
      /** used for mutex tournament, includes priorand */
      val prio=addLt(delayedL(prioRand::flipAndPrioCreatedByMoves._1))
      /** flipAndPrioCreatedByMoves stores its results in order not to be called two times */
      val flipOfMove:BoolV=delayedL(flipAndPrioCreatedByMoves._2)
      val highestTriggered:UintV=delayedL(flipAndPrioCreatedByMoves._3)

   */

   /** PEs where movements trigger changes in Agent's support. Either by filling, or by emptying
    flip is eith computed from the move for movableAgent, or  computed from the parent for bounded agent
    registers where the constraints had a canceling effect*/
   val flipCancel=  new scala.collection.mutable.LinkedHashMap[String,BoolV]() with Named {}
   /** applies all the constraints on the move */
   val  allFlipCancel: ASTLt[V, UI] ={
     /** computes an IntVUI  whose individual bits are cancel Flips  */
     def allFlipCancel(flip: BoolV): UintV = {
       for ((name, c) <- constrs) {
         flipCancel(name) = ~c.where & flip //where also takes into account flipOfMove
       }
       val allFlipCancel: Array[UintV] = flipCancel.values.toArray.map(_.asInstanceOf[UintV])
       allFlipCancel.reduce(_ :: _)
     }
     delayedL( allFlipCancel(flipOfMove))
   }
   // val f:BoolV=False()
     val noFlipCancel=eq0(allFlipCancel)
     val flipAfterLocalConstr: BoolV = noFlipCancel  & flipOfMove



  /** used for computing flip cancelation depending on impact */
  val isV: BoolV
   /** can be defined on agent, but needs a delayed for isV is not known yet */
  val NisV :BoolV= not(delayedL(isV))
  /** applying constraints identifies PEs where flip should be canceled, cancelFlip will implement this cancelation */

/////////////we now describe class for easily adding constraint, they are subclass of agents, in order to use the agent's field isV, NisV, and more.

   /**
    *
    * @param ags one or two agents on which to apply constraint
    *            Constr is an inner classes of agents, so that it can access its main agent's field.
    */

   abstract class Constr(val ags: Array[Agent[_ <: Locus]], val impact: Impact, flip:BoolV) {
     /** where = places where flips is still valid after the constraint newFlip<-olcFlip&where
      * defined has a method, in order allow definition prior to intanciation of needed field, such as flip.*/
     val where: BoolV //will use fields from the agent: flip, as well as this
   }

   class KeepFlipIf(i: Impact,val loc:BoolV,flip:BoolV) extends Constr(Array(this), i,flip)
   { override val where: BoolV = impact match {
     case Both() => loc
     case One(v) =>  implique (if (v) isV else (NisV),loc)
   }
   }
   /** Same as KeepFlipIf, exept that now, loc is a method, so that the constraint can be
    * defined at a moment where loc is not known*/

   class CancelFlipIf(i: Impact, l:BoolV,flip:BoolV) extends KeepFlipIf(i,~l,flip)

   /**
    *
    * @param i
    * @param mutex not more than one will flip each side of mutex
    */
   class MutKeepFlipIf(i: Impact,val mutex:BoolE,flip:BoolV) extends Constr(Array(this), i,flip) {
     /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
     def mutrig:BoolE =mutex &  (impact  match {
       case Both() => insideS(flip)
       case One(v) =>  insideS(flip & (if (v) isV else (NisV))) // result also depend on impact
     })
     /** flip is ok if prio is minimum with respect to the other side */
     def tmp: ASTLt[T[E, V], B] =imply(v(mutrig),ags.head.prio.gt)
     /** flip is preserved if no neighbor edge present a problem */
     val where=inside(transfer(tmp))
   }
   class MutCancelFlipIf(i: Impact,val mutex:BoolE,flip:BoolV) extends Constr(Array(this), i,flip) {
     /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
     def mutrig:BoolE =mutex &  (impact  match {
       case Both() => insideS(flip)
       case One(v) =>  insideS(flip & (if (v) isV else (NisV))) // result also depend on impact
     })
     /** flip is ok if prio is minimum with respect to the other side */
     def tmp=imply(v(mutrig),prio.gt)
     val where=inside(transfer(~tmp))
   }
   /**
    *
    * @param i
    * @param mutex not more than one will flip each remote (apex) side
    */
   class MutApexKeepFlipIf(i: Impact,val mutex:BoolE,flip:BoolV) extends Constr(Array(this), i,flip) {
     /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
       val mutrig:BoolE ={
       mutex &  (impact  match {
         case Both() => inside(apexE(f(flip)))
         case One(v) =>  inside(apexE(f(flip & (if (v) isV else (NisV)))))// result also depend on impact
       });
       // mutrigv.name="fliesMutrigv";      mutrigv
     }

     /** flip is ok if prio is smaller with respect to the other side */
     val chekLtIfMutrig=imply(f(mutrig),prio.ltApex)
     val where=inside(apexV(chekLtIfMutrig))
   }
   /**
    *
    * @param i
    * @param mutex not more than one will flip each side of mutex
    */
   class TriKeepFlipIf(i: Impact,val tritex: BoolF,flip:BoolV) extends Constr(Array(this), i,flip) {
     /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
     val tritrig:BoolF =tritex &  (impact  match {  //y a moyen d'écrire un trigger générique pour mut,tri, et loc
       case Both() => insideS(flip)
       case One(v) =>  insideS(flip& (if (v) isV else (NisV))) // result also depend on impact
     })
     /** flip is ok if prio is minimum with respect to the other side */
     def tmp: BoolVf =imply(transfer(v(tritrig)),ags.head.prio.gt3)
     /** flip is preserved if no neighbor edge present a problem */
     val where=inside(tmp)
   }




 }
