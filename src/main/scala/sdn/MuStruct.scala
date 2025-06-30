package sdn

import compiler.AST.{Layer, Strate}
import compiler.SpatialType.BoolV
import compiler.repr.{nomB, nomV}
import compiler.{AST, ASTBt, ASTL, ASTLfun, ASTLt, B, CallProc, Circuit, Locus, Ring, V, repr}
import dataStruc.{BranchNamed, DagNode, Named}
import dataStruc.DagNode.EmptyBag
import sdn.Agent

import scala.Predef.->
import scala.collection.immutable.HashMap
/** allow to use system instruction (show, debug...) by adding them to selected AST, so that the compiler can retrieve them
 * previously only layers could use system instructions, but it turns out to be not sufficient*/
trait carrySysInstr{
  var syysInstr: List[CallProc] = List.empty;
}
/** allows to retrieve system instructions: shoow, buugif... */
/*trait SyysInstr{
  //self:AST[_]=>
  var syysInstr: List[CallProc] = List.empty;
  /** @param v field to be displayed   */
  protected def shoow(v: AST[_]*) = {
    for (f <- v)
      syysInstr ::= CallProc("show", List(), List(f))
  }
  /** @param v field that should be false everywere unless a bug appears */
  def buugif(v: AST[_]) = syysInstr ::= CallProc("bug", List(), List(v))
}*/


/**
 un element du LDAG, sert a updater toutes les trucs dans l'ordre. */
abstract class MuStruct[L<:Locus,R<:Ring] extends  DagNode[MuStruct[_<:Locus,_<:Ring]] with Named with BranchNamed {
  //self: AST[(L,B)] =>

  /** support of agent */
val is: Strate[(L,R)] with ASTLt[L,R] with carrySysInstr
  /** we add the possibility to display fields */
  protected def shoow(v: AST[_]*) = {
    for (f <- v)
      is.syysInstr ::= CallProc("show", List(), List(f))
  }
  protected def shoowText(v: AST[_],ls:String*)={
    is.syysInstr ::= CallProc("show", List(), List(v))
    Circuit.labelsOfFieldsBeforeName=Circuit.labelsOfFieldsBeforeName + ((v , ls.toList))
  }
  protected def shoowText(v: AST[_],ls:List[String])={
    is.syysInstr ::= CallProc("show", List(), List(v))
    Circuit.labelsOfFieldsBeforeName=Circuit.labelsOfFieldsBeforeName + ((v , ls))
  }


  /** we add the possibility  to declare invariant */
  protected def buugif(v: AST[_]) = {
      is.syysInstr ::= CallProc("bug", List(), List(v))
  }
  def locus: Locus =is.locus//todo, on pourrait calculer cela directement

}


/** Bound agent need not layers */
//abstract class BoundAg[L<:Locus] extends Agent[L]
/** movable agent stores their chi in a layer, in order to be able to modify it. */

object MuStruct{


  //def const[L <: Locus, R <: Ring](cte: ASTBt[R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = Coonst(cte, m, n)


}
