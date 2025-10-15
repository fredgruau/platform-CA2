package sdn

import compiler.AST.{Layer, delayed}
import compiler.ASTL.{ASTLg, delayedL}
import compiler.SpatialType.BoolV
import compiler.repr.{nomB, nomV}
import compiler.{AST, ASTBt, ASTL, ASTLfun, ASTLt, B, CallProc, Circuit, Locus, Ring, SI, V, repr}
import dataStruc.{BranchNamed, DagNode, Named}
import dataStruc.DagNode.EmptyBag
import sdn.Agent
import sdn.MuStruct.allMuStruct

import scala.Predef.->
import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.mutable
/** allow to use system instruction (show, debug...) by adding them to selected AST, so that the compiler can retrieve them
 * previously only layers could use system instructions, but it turns out to be not sufficient*/

trait carrySysInstr{
  var syysInstr: List[CallProc] = List.empty;
}

trait hasMuisSysInstr{
  val muis:ASTLg with carrySysInstr}

/** si une classe posséde un muis qui a une liste de sysinstr, on peut faire les shoow, bugif, showtext, en les rangeant dans cette liste */
trait shoow{
  self:hasMuisSysInstr=>
  def buugif(v: AST[_]) = {muis.syysInstr ::= CallProc("bug", List(), List(v))  }
  def shoow(vs: AST[_]*) = {for (v <- vs)   muis.syysInstr ::= CallProc("show", List(), List(v)) }
  def shoowText(v: AST[_],ls:List[String])={  muis.syysInstr ::= CallProc("show", List(), List(v))
    Circuit.labelsOfFieldsBeforeName=Circuit.labelsOfFieldsBeforeName + ((v , ls))
  }

}

 class LDAG{
  /** this enables to deliver compute root, which is allways the first mustruc*/
  def  particle=allMuStruct.head
}
/** transform a layer into strate, to fit in the mustruct hierarchy */
trait Stratify[L<:Locus,R<:Ring] extends ASTL.Strate[L,R] {
  self: Layer[(L, R)] =>
  val pred=this.asInstanceOf[ASTLt[L,R]]
  //todo faire a l'envers: on defini munext, et on dit que next = delayed munext
  override val munext: ASTLt[L, R] =delayedL(this.next.asInstanceOf[ASTLt[L,R]])(self.mym) }

/** we add trait carrySysInstr to layers so as to fit mustruct logic of using layers as strates, and to store system instructions  */
abstract class LayerS[L<:Locus,R<:Ring](override val nbit: Int, override val init: String)(implicit m: repr[L],n:repr[R])
  extends Layer[(L,R )](nbit,init)with Stratify[L,R] with ASTLt[L,R] with carrySysInstr()

/** si mixé avec, transforme une layer en mustruct */
//trait LayerToStrate[L<:Locus,R<:Ring] extends  Stratify[L,R] with ASTLt[L,R] with carrySysInstr  { this: AST.Layer[(L,R)] =>}

/** un element du LDAG, sert a updater toutes les trucs dans l'ordre,
 * le path de nommage passe par les mustruct, et plus par les layers.
 * pour cela on mix les trait branchname et name */
abstract class MuStruct[L<:Locus,R<:Ring] extends  DagNode[MuStruct[_<:Locus,_<:Ring]]
  with Named with BranchNamed with hasMuisSysInstr with shoow {
  //self: AST[(L,B)] =>
  allMuStruct.append( this) //insert new created muStruct on  last position of already instanciated mu struct
  /** support of agent, implemented as a layer. we also use it to store a list  of system instructions */
val muis: ASTL.Strate[L,R] with ASTLt[L,R] with carrySysInstr
  /** we add the possibility to display fields */
  def locus: Locus =muis.locus//todo, on pourrait calculer cela directement
}

trait muEmptyBag extends EmptyBag[MuStruct[_ <: Locus, _ <: Ring]]
/** Bound agent need not layers */
//abstract class BoundAg[L<:Locus] extends Agent[L]
/** movable agent stores their chi in a layer, in order to be able to modify it. */

object MuStruct{
   var allMuStruct:mutable.ArrayDeque[MuStruct[_<:Locus,_<:Ring]]=mutable.ArrayDeque()
  /** we can display mustruct only after DataProg has been built and names have been given using reflection */
   def showMustruct=for(m<-allMuStruct)
     System.out.println(m.toString)
   //def setFlipofMove()=  for(m<-allMuStruct)   if(m.isInstanceOf[Agent])

   //var sortedMuStruct:List[MuStruct[_<:Locus,_<:Ring]]=List()

  //def const[L <: Locus, R <: Ring](cte: ASTBt[R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = Coonst(cte, m, n)


}
