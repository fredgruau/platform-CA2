package sdn

import compiler.ASTB.{False, Uint}
import compiler.ASTBfun.{addRedop, derivative, ltUI2, orRedop, redop}
import compiler.ASTL.{delayedL, send, transfer, unop}
import compiler.ASTLfun.{allOne, andLB2R, b2SIL, e, eq0, f, imply, lt2, ltSI, neq, orScanRight, reduce, uI2SIL, v}
import compiler.SpatialType.{BoolE, BoolEv, BoolF, BoolV, BoolVe, BoolVf, IntE, IntEv, IntV, IntVe, UintV, UintVx}
import compiler.repr.nomE
import compiler.{ASTLfun, ASTLt, B, E, F, Locus, SI, T, UI, V, chip}
import dataStruc.{BranchNamed, Named}
import progOfCA._
import progOfLayer.Sextexrect.chooseMaxOf
import progOfmacros.Comm.{apexE, apexV, neighborsSym}
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




/** an entity such has a boolV atents or more generally a mustruct, which provide hasIsV, can be completed with utilAgent */
trait HasIsV{
/** used for computing flip cancelation depending on impact of constraint, so that constraint can act non only
 * which can be both(),  noFill(true) noFill(false)
 * case class One(noFill: Boolean) extends Impact
 * on veut pouvoir calculer le complementaire d'une contraint, forbid et oblige sont complementaire
 *  not only for BoolV Agent, but also for Ev Agents */
val isV: BoolV
/** can be defined on agent, delayed is needed because  isV is not known yet */
val NotIsV :BoolV= ~(delayedL(isV))
}


/**
 * agents are boolean muStruct
 * @tparam L  locus of the agent's support, we can have Vagent L=V, Ve AgentsL=Ve, ....
 * For the moment we consider that all agents extend hasIsv, it may be the case that E-agents, do not.
 */
abstract class Agent[L <: Locus] extends MuStruct[L, B] with HasIsV
 {

/** the agent's list of consrtrain. Constraints have a name, and the list is also ordered */
   //val constrs= new scala.collection.mutable.LinkedHashMap[String,Constr]()
   /** the agent's list of consrtrain, but before we know flip */
   val constrs2= new scala.collection.mutable.LinkedHashMap[String,BoolV=>Constr]()
   def codeConstraint: Iterable[String] =constrs2.keys.toList.map(_.charAt(0).toString)
   /** shows a letter corresponding to the constraint, for all constraint which effectively contribute in reducing flip */
   def showConstraint={ shoowText(allFlipCancel,codeConstraint.toList);
     //shoow(tataaaa)
   }
   def codeMove:Iterable[String] = {
     assert(moves.size>1,"faut au moins deux move, sinon pb entier codé par un bool")
     moves.map(_.keys.head.charAt(0).toString)
   }


   /** will not show move that block movement instead of trigering it */
   def showPositiveMoves={ shoowText(yesHighestTriggered,codeMove.toList)}
   /** shows also blocking moves */
   def showMoves={ shoowText(highestTriggered,codeMove.toList)}
   def showFlip=shoow(flipOfMove, flipAfterLocalConstr)
 /** test que les var s'affiche bien */
  // var muuis:BoolV=   ~ (~ delayedL( isV))
   def showMe={

     shoow(muis);showPositiveMoves;showConstraint;showFlip;
     showPrio
   }
   /**
    * @param name more explicit name
    * @param shortName used for display in CApannel
    * @param c constraint
    */
 /*def constrain(name:String, shortName:Char, c: Constr) = {
   if(constrs.contains(shortName+name))
     throw new Exception("une contrainte du nom "+name+" exite déja, changez le nom siou plait")
   constrs(shortName+name)=c
 }*/
   def constrain2(name:String, shortName:Char, c: BoolV=>Constr) = {
   if(constrs2.contains(shortName+name))
     throw new Exception("une contrainte du nom "+name+" exite déja, changez le nom siou plait")
   constrs2(shortName+name)=c
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
   /** not the same for  movable/bound  */
   def allTriggered:UintV;
   def allTriggeredYes:UintV
   /** does a computation to be repeated specifically for yes moves */
   def processMoves(all:UintV):(UintV,UintV,UintV)={
     /** bouche les trouvs avec un orscanrigh */
     val filled=orScanRight(all)
     (filled,unop(derivative, filled),unary2Bin(filled))
   }

   /**  */
   def setFlipOfMove()={}

   val (filledTriggered,/** all false except for highest priority move*/highestTriggered,
   prioDet)=processMoves(delayedL(allTriggered))
   /** selectionne le flip parmis les flip des mouvement proposés */
   val flipOfMove=neq(highestTriggered&delayedL(allFlip))

   /** makes a global logical or, of boolean which are true for C2moves,
    *  if false then there will not be negative move
    *  and */
   lazy val presentOfC2moves=moves.map(_.values.map(
     {
       case a:MoveC2=>
         true
     case a:MoveC1=>
       false}
   ).reduce( _ | _)).reduce( _| _)


   /** on le fait aussi pour les "yes" move */
   val (yesFilledTriggered,yesHighestTriggered,yesPrioDet)=
     if(false/*presentOfC2moves*/)(filledTriggered,highestTriggered, prioDet)
     else processMoves(delayedL(allTriggeredYes))
   /** flips for all priorities */
   def allFlip:UintV

   /** selected positive move has lower priority than selected move, implies quiescence */
   val isQuiescent:BoolV =lt2(yesPrioDet,prioDet)
   /** flip real takes into account negative moves by maintaining flip only for non quiescent vertice */
   val flipReal=flipOfMove & ~isQuiescent
   /**  adds a bit of randomnes to forces's priority
    * allows to  breaking  symetry in case of tournament with equal force's priority */
   val prioRand:UintV
    val prio: UintVx =addLt(prioRand::prioDet)
   def showPrio={shoowText(prioRand,List()); shoowText(prio,List())}

   val prioYes: UintVx =addLt(prioRand::yesPrioDet)
   /** nullify prio if vertice is quiescent we are interested only in high prio only if move is generated
    * this priority is the one to be used when evaluationg local constraints*/
   val prioYesNotQuiescent=addLt(andLB2R(~ isQuiescent, prioYes))

   /** PEs where movements trigger changes in Agent's support. Either by filling, or by emptying
    flip is eith computed from the move for movableAgent, or  computed from the parent for bounded agent
    registers where the constraints had a canceling effect*/
   val flipCancel=  new scala.collection.mutable.LinkedHashMap[String,BoolV]() with Named {}

   /** applies all the constraints on the move */
   val  allFlipCancel: ASTLt[V, UI] ={
     /** computes an IntVUI  whose individual bits are cancel Flips  */
     def allFlipCancel(flip: BoolV): UintV = {
       //ancien a virer bientot
   /*    for ((name, c) <- constrs) {
         flipCancel(name) = ~c.where & flip //where also takes into account flipOfMove
       }*/
       for ((name, c) <- constrs2)
         flipCancel(name) = ~c(flip).where & flip //where also takes into account flipOfMove
       val allFlipCancel: Array[UintV] = flipCancel.values.toArray.map(_.asInstanceOf[UintV])
       allFlipCancel.reduce(_ :: _)
     }
     //delayedL( allFlipCancel(flipOfMove))
     delayedL( allFlipCancel(flipReal))
   }
   // val f:BoolV=False()
     val noFlipCancel=eq0(allFlipCancel)
     val flipAfterLocalConstr: BoolV = noFlipCancel  & flipOfMove
     val highproba= root4naming.addRandBit().asInstanceOf[BoolV]| root4naming.addRandBit().asInstanceOf[BoolV]
     val flipRandomlyCanceled=flipAfterLocalConstr //& highproba //decommenter pour annuler au hasard, utilise pour casser les cycles



  /** applying constraints identifies PEs where flip should be canceled, cancelFlip will implement this cancelation */

/////////////we now describe class for easily adding constraint, they are subclass of agents, in order to use the agent's field isV, NisV, and more.

   /**
    *
    * @param ags one or two agents on which to apply constraint
    *            Constr is an inner classes of agents, so that it can access its main agent's field such as prio.
    */

   abstract class Constr(val ags: Array[Agent[_ <: Locus]], val impact: Impact, flip:BoolV) {
     /** where = places where flips is still valid after the constraint newFlip<-olcFlip&where
      * defined has a method, in order allow definition prior to intanciation of needed field, such as flip.*/
     val where: BoolV //will use fields from the agent: flip, as well as this
   }



   class KeepFlipIf(i: Impact,val loc:BoolV,flip:BoolV) extends Constr(Array(this), i,flip)
   { override val where: BoolV = impact match {
     case Both() => loc    case One(v) =>  implique (if (v) isV else (NotIsV),loc)   }   }
    object KeepFlipIf{def apply(i: Impact, l:BoolV)(flip:BoolV): KeepFlipIf = new KeepFlipIf(i,l,flip)}


   class CancelFlipIf(i: Impact, l:BoolV,flip:BoolV) extends KeepFlipIf(i,~l,flip)
   object CancelFlipIf{def apply(i: Impact, l:BoolV)(flip:BoolV): CancelFlipIf = new CancelFlipIf(i,l,flip)   }
   /**
    *
    * @param i
    * @param mutex not more than one will flip each side of mutex
    */
   class MutKeepFlipIf(i: Impact,val mutex:BoolE,flip:BoolV) extends Constr(Array(this), i,flip) {
     /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
     def mutrig:BoolE =mutex &  (impact  match {
       case Both() => insideS(flip)
       case One(v) =>  insideS(flip & (if (v) isV else (NotIsV))) // result also depend on impact
     })
     /** flip is ok if prio is maximum with respect to the other side */
     def tmp: BoolEv =imply(v(mutrig),ags.head.prioYesNotQuiescent.gt) //todo faut mettre lt
     /** flip remains ok if no neighbor edge present a problem */
     val ttmp=tmp
     val where: BoolV =inside(transfer(ttmp))
   }
   object MutKeepFlipIf{def apply(i: Impact, mutex:BoolE)(flip:BoolV): MutKeepFlipIf = new MutKeepFlipIf(i,mutex,flip) }
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
         case One(v) =>  inside(apexE(f(flip & (if (v) isV else (NotIsV)))))// result also depend on impact
       });
       // mutrigv.name="fliesMutrigv";      mutrigv
     }

     /** flip is ok if prio is smaller with respect to the other side */
     //  val chekLtIfMutrig=imply(f(mutrig),prio.ltApex) // je mettait lt au lieu de gt, cela peut créer des oscillations.
     val chekLtIfMutrig=imply(f(mutrig),prio.gtApex)
     val where=inside(apexV(chekLtIfMutrig))
   }
 object MutApexKeepFlipIf{def apply(i: Impact, mutex:BoolE)(flip:BoolV): MutApexKeepFlipIf = new MutApexKeepFlipIf(i,mutex,flip) }
   class TriKeepFlipIf(i: Impact,val tritex: BoolF,flip:BoolV) extends Constr(Array(this), i,flip) {
     /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
     val tritrig:BoolF =tritex &  (impact  match {  //y a moyen d'écrire un trigger générique pour mut,tri, et loc
       case Both() => insideS(flip)
       case One(v) =>  insideS(flip& (if (v) isV else (NotIsV))) // result also depend on impact
     })
     /** flip is ok if prio is minimum with respect to the other side */
     def tmp: BoolVf =imply(transfer(v(tritrig)),ags.head.prio.gt3)
     /** flip is preserved if no neighbor edge present a problem */
     val where=inside(tmp)
   }
object TriKeepFlipIf{def apply(i: Impact, tritex: BoolF)(flip:BoolV): TriKeepFlipIf = new TriKeepFlipIf(i,tritex,flip) }



 }
