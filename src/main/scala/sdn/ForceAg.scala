package sdn

import compiler.AST.Layer
import compiler.ASTB.{False, Uint}
import compiler.ASTBfun.{addRedop, derivative, ltUI2, orRedop, redop}
import compiler.ASTL.{delayedL, send, transfer, unop}
import compiler.ASTLfun.{allOne, andLB2R, b2SIL, e, eq0, f, fromBool, imply, lt2, ltSI, neighbors, neq, orScanRight, reduce, uI2SIL, v}
import compiler.SpatialType.{BoolE, BoolEv, BoolF, BoolV, BoolVe, BoolVf, IntE, IntEv, IntV, IntVe, UintV, UintVx}
import compiler.repr.nomE
import compiler.{AST, ASTLfun, ASTLt, B, E, F, Locus, SI, T, UI, V, chip, repr}
import dataStruc.{BranchNamed, Named}
import progOfCA._
import progOfLayer.Sextexrect.chooseMaxOf
import progOfmacros.Comm.{apexE, apexV, neighborsSym}
import progOfmacros.{Compute, Grad, Wrapper}
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
case class
One(noFill: Boolean) extends Impact //on veut pouvoir calculer le complementaire d'une contraint, forbid et oblige sont complementaire




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
* agents are boolean muStruct udated using force
  * * @tparam L  locus of the agent's support, we can have Vagent L=V, Ve AgentsL=Ve, ....
* For the moment we consider that all agents extend hasIsv, it may be the case that E-agents, do not.
  */
abstract class Agent[L <: Locus] extends MuStruct[L, B] with HasIsV {
  /** also used by DetectedAg */
  var flipAfterLocalConstr: BoolV=null
  var flipRandomlyCanceled: BoolV=null
  /**  */
}

trait keepInsideForce {
  self : Agent[V]=>
  /** place where new self appears */
  val nouveau= muis.munext & ~muis.pred
  val alreadyThere=muis.munext & muis.pred

  /** if there is an ag present next to nouveau , it will be pushed to fill the nouveau
   * noneed to empty whatever, so empty remains false.  */
  def keepInside:Force=  new Force() {
    override def actionV(ag: MovableAgV): MoveC = {
      /** the surrounding agent does not yet contain nouveau */
      val nouveauToFill = nouveau & ~ag.muis
      /** if not null will create a push in order to fill nouveau which are not yet filled */
      val push=neighbors(nouveauToFill) & e(ag.muis)
      val coveredByPush=exist(neighborsSym(push))
      /** should be true everywhere */
      val nouveauIsFilled: BoolV =imply(coveredByPush,nouveauToFill)
      val oui = MoveC1(fromBool(false), push)
      /** we must not empty voronoi in places where it will contain gcenters*/
      val non = MoveC1(alreadyThere&ag.muis,e(fromBool(false)))
      MoveC2(oui,non)
    }
  }
}





/** detected Agents directly compute their next state using a field called "detected"
 * they are not really agent because they do not undergo forces.
 * we can compute deflipSimult, also for those agents, in order to check that no deflip will apply*/
abstract class DetectedAgV ( val detected: BoolV )  extends Agent[V] {
  /** support of agent, implemented as a layer. we also use it to store a list  of system instructions */
  override val muis=new Layer[(V, B)](1, "global") with ASTLt[V,B]  with Stratify [V,B] with carrySysInstr   {
    override val  next = detected  }
  override val isV: BoolV = muis
  //artificially reconstructed, we will be able to watch if it happens to be canceled by simult constraint
   flipAfterLocalConstr=muis ^ muis.next
  def showme={shoow(detected)}
}

//class Gcenter(arg: ) extends DetectedAgV


/**  agentsF are Agents  udated using force */
abstract class ForceAg[L <: Locus] extends Agent[L]
 {

/** the agent's list of consrtrain. Constraints have a name, and the list is also ordered */
   val constrs= new scala.collection.mutable.LinkedHashMap[String,PartialUI =>Constr]()
   /** stores the first letter of each constraint's name. This lettre is to be displayed on vertice where constraint is active
    * there can be several active constraints*/
   def codeConstraint: Iterable[String] =constrs.keys.toList.map(_.charAt(0).toString)
   /** shows a letter corresponding to the constraint, for all constraint which effectively contribute in reducing flip */
   def showConstraint={ shoowText(allFlipCancel,codeConstraint.toList);  }

   /** stores the first letter of each move's name for all priorities, This lettre is to be displayed if move is selected
    * there can be at  most  one positive move selected
    * if move is blocking nothing get displayed, and  isquiscent will be true */
   def codeMove:Iterable[String] = { assert(moves.size>1,"faut au moins deux move, sinon pb entier codé par un bool")
     moves.map(_.keys.head.charAt(0).toString) }

   /** will show only move that trigger movement. Move that "block" movement are hidden,  */
   def showPositiveMoves={
     shoowText(yesHighestTriggered,codeMove.toList)
     shoowText(allBugs,codeMove.toList)
   }
   // /** shows also  moves that block movement */
  // def showMoves={ shoowText(highestTriggered,codeMove.toList)}
   def showFlip={
     shoowText(
       fliprioOfMove.valuc, List()
     )
     shoow(fliprioOfMove.valuc.lt)
     shoow(fliprioOfMove.defined, isQuiescent, flipAfterLocalConstr)
   }
 /** test que les var s'affiche bien */
   def showMe={showPositiveMoves;showConstraint;showFlip;}
   /**
    * @param name more explicit name
    * @param shortName used for display in CApannel
    * @param c constraint to be added to the list of agent's constraint
    *          it is a function because at the time of adding the constraint, prio and flip are no known yet
    */
   def addConstraint(name:String, shortName:Char, c: PartialUI=>Constr) = {
   if(constrs.contains(shortName+name))    throw new Exception("une contrainte du nom "+name+" exite déja, changez le nom siou plait")
   constrs(shortName+name)=c  }
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
   def allBug:UintV;
   def allTriggeredYes:UintV
   /** flips for all priorities */
   def allFlip:UintV
  //variable defined when computing fliprioOfMove
   var isQuiescent:BoolV=null
   var yesHighestTriggered:UintV=null
   var allBugs:UintV=null
   /**  adds a bit of randomnes to forces's priority
    * allows to  breaking  symetry in case of tournament with equal force's priority */
   val prioRand:UintV
   var fliprioOfMove:PartialUI=null
   /**  */
   def setFliprioOfMove() = {
     /** does a computation to be repeated specifically for yes moves */
     def processMoves(all:UintV):(UintV,UintV,UintV)={
       /** bouche les trous avec un orscanrigh */
       val filled=orScanRight(all)
       (filled,unop(derivative, filled),unary2Bin(filled))
     }
     val (filledTriggered,/** all false except for highest priority move */ highestTriggered, prioDet) =
       processMoves(allTriggered)
     /** selectionne le flip parmis les flip des mouvement proposés */
     val flipOfMove = neq(highestTriggered & allFlip)

     /** on le fait aussi pour les "yes" move */
     val (yesFilledTriggered, yHT, yesPrioDet) = {
       /** makes a global logical or, of boolean which are true for C2moves,
        * if false then there will not be negative move
        * and yesFilledtriggered is equal to fill triggered, thereby simplifying the computation*/
       val presenceOfC2moves = moves.map(_.values.map({case a: MoveC2 =>true  case a: MoveC1 =>  false} ).reduce(_ | _)).reduce(_ | _)
       if (!presenceOfC2moves ) (filledTriggered, highestTriggered, prioDet)
       else processMoves(allTriggeredYes)
     }
     allBugs=allBug
     yesHighestTriggered = yHT //used for printable purpose
     /** selected positive move has lower priority than selected move, implies quiescence */
     isQuiescent = lt2(yesPrioDet, prioDet)
     val prioYes: UintV = prioRand :: yesPrioDet
     /** nullify prio if vertice is quiescent we are interested only in high prio only if move is generated
      * this priority is the one to be used when evaluationg local constraints */
     val prioYesNotQuiescent = addLt(andLB2R(~isQuiescent, prioYes))
     fliprioOfMove=new PartialUI(flipOfMove, prioYesNotQuiescent)
   }
  //setFliprioOfMove() //this is now done separately

   /** PEs where movements trigger changes in Agent's support. Either by filling, or by emptying
    flip is eith computed from the move for movableAgent, or  computed from the parent for bounded agent
    registers where the constraints had a canceling effect*/
   val flipCancel=  new scala.collection.mutable.LinkedHashMap[String,BoolV]() with Named {}
   val highproba= root4naming.addRandBit().asInstanceOf[BoolV]| root4naming.addRandBit().asInstanceOf[BoolV]

   /** applies all the constraints on the move */
   var  allFlipCancel: UintV = null
     /** computes an IntVUI  whose individual bits are cancel Flips  */
     def allFlipCancel(fliprio: PartialUI): UintV = {
       for ((name, c) <- constrs)   flipCancel(name) = ~c(fliprio).where & fliprio.defined //where also takes into account flipOfMove
       val allFlipCancel: Array[UintV] = flipCancel.values.toArray.map(_.asInstanceOf[UintV])
       allFlipCancel.reduce(_ :: _)
     }

   def setFlipCancel()= {
     //we separate local, mutex, mutapex, tritex, sextex
     val local=constrs.filter(_._2.isInstanceOf[KeepFlipIf])
     var mut=constrs.filter(_._2.isInstanceOf[KeepFlipIf])
     allFlipCancel=allFlipCancel(fliprioOfMove)
     val noFlipCancel=eq0(allFlipCancel)
     flipAfterLocalConstr = noFlipCancel  & fliprioOfMove.defined
     flipRandomlyCanceled=flipAfterLocalConstr //& highproba //decommenter pour annuler au hasard, utilise pour casser les cycles
   }
   //setFlipCancel() //this is now done one Mustruct
  /** applying constraints identifies PEs where flip should be canceled, cancelFlip will implement this cancelation */
///we now describe class for easily adding constraint, they are subclass of agents, in order to use the agent's field isV,
   // NisV, and more. They used an object to defined an apply method allowing to curify the function , because fliprio is not available yet
   /** @param ags one or two agents on which to apply constraint
    *            Constr is an inner classes of agents, so that it can access its main agent's field such as prio.
    */
   abstract class Constr(val ags: Array[ForceAg[_ <: Locus]], val impact: Impact, fliprio:PartialUI) {
     /** where = places where flips is still valid after the constraint newFlip<-olcFlip&where
      * defined has a method, in order allow definition prior to intanciation of needed field, such as flip.*/
     val where: BoolV //will use fields from the agent: flip, as well as this
   }
   class KeepFlipIf(i: Impact,val loc:BoolV,fliprio:PartialUI) extends Constr(Array(this), i,fliprio) { override val where: BoolV =
     impact match {
     case Both() => loc    case One(v) =>  implique (if (v) isV else (NotIsV),loc)   }   }
    object KeepFlipIf{def apply(i: Impact, l:BoolV)(fliprio:PartialUI): KeepFlipIf = new KeepFlipIf(i,l,fliprio)}

   class CancelFlipIf(i: Impact, l:BoolV,fliprio:PartialUI) extends KeepFlipIf(i,~l,fliprio)
   object CancelFlipIf{def apply(i: Impact, l:BoolV)(fliprio:PartialUI): CancelFlipIf = new CancelFlipIf(i,l,fliprio)   }
   /**
    *
    * @param i
    * @param mutex not more than one will flip each side of mutex
    */
   class MutKeepFlipIf(i: Impact,val mutex:BoolE,val fliprio:PartialUI) extends Constr(Array(this), i,fliprio) {
     /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
     def mutrig:BoolE =mutex &  (impact  match {
       case Both() => insideS(fliprio.defined)
       case One(v) =>  insideS(fliprio.defined & (if (v) isV else (NotIsV))) // result also depend on impact
     })
     /** flip is ok if prio is maximum with respect to the other side */
     def tmp: BoolEv =imply(v(mutrig),fliprio.valuc.lt) //todo faut mettre lt?oui, lt est vrai du coté de la plus grosse prio
     /** flip remains ok if no neighbor edge present a problem */
     val ttmp=tmp
     val where: BoolV =inside(transfer(ttmp))
   }
   object MutKeepFlipIf{def apply(i: Impact, mutex:BoolE)(fliprio:PartialUI ): MutKeepFlipIf = new MutKeepFlipIf(i,mutex,fliprio) }
     /**
    *
    * @param i
    * @param mutex not more than one will flip each remote (apex) side
    */
   class MutApexKeepFlipIf(i: Impact,val mutex:BoolE,fliprio:PartialUI ) extends Constr(Array(this), i,fliprio) {
     /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
     val mutrig:BoolE ={
       mutex &  (impact  match {
         case Both() => inside(apexE(f(fliprio.defined)))
         case One(v) =>  inside(apexE(f(fliprio.defined & (if (v) isV else (NotIsV)))))// result also depend on impact
       })}
     /** flip is ok if prio is smaller with respect to the other side */
     //  val chekLtIfMutrig=imply(f(mutrig),prio.ltApex) // je mettait lt au lieu de gt, cela peut créer des oscillations.
     val chekLtIfMutrig=imply(f(mutrig),fliprio.valuc.ltApex)
     val where=inside(apexV(chekLtIfMutrig))
   }
 object MutApexKeepFlipIf{def apply(i: Impact, mutex:BoolE)(fliprio:PartialUI): MutApexKeepFlipIf =
       new MutApexKeepFlipIf(i,mutex,fliprio) }
   class TriKeepFlipIf(i: Impact,val tritex: BoolF,fliprio:PartialUI) extends Constr(Array(this), i,fliprio) {
     /** mutex is triggered if there is indeed two flips on each side of the mutex, and in the right state. */
     val tritrig:BoolF =tritex &  (impact  match {  //y a moyen d'écrire un trigger générique pour mut,tri, et loc
       case Both() => insideS(fliprio.defined)
       case One(v) =>  insideS(fliprio.defined& (if (v) isV else (NotIsV))) // result also depend on impact
     })
     /** flip is ok if prio is minimum with respect to the other side */
     def tmp: BoolVf =imply(transfer(v(tritrig)),fliprio.valuc.gt3)
     /** flip is preserved if no neighbor edge present a problem */
     val where=inside(tmp)
   }
object TriKeepFlipIf{def apply(i: Impact, tritex: BoolF)(fliprio:PartialUI): TriKeepFlipIf =
  new TriKeepFlipIf(i,tritex,fliprio) }

 }
