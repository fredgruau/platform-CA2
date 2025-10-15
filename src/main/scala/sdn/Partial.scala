package sdn

import compiler.ASTLfun.andLB2R
import compiler.SpatialType.{BoolV, UintV, UintVx}
import compiler.{ASTL, ASTLt, B, Locus, Ring, UI, V, repr}
import sdn.Util.addLt

/**
 *
 * @param defined true if value is defined
 * @param value actual partially defined value
 * @tparam R  ring can be signed, unsigned int, or bool
 * we very often use partially defined value, defining a class for it allows to regroup all the code for this.
 * the main exemple is to group flip and prio, because prio is relevant only if flip is true.
 * invariant dans ce cas est defined=false=>value=0
 * si l'invariant n'est pas verifié, on peut le restored en faisant value = andlbtoR( defined, value)
 */
class PartialASTL[ R <: Ring](val defined:BoolV, val value:ASTLt[V,R])(implicit m:repr[R]) {
  def restoreInvariant: ASTLt[V, R] = andLB2R(defined, value)
}

class PartialUI (override val defined:BoolV, override val value:UintV)extends PartialASTL[UI](defined,value){
   val valuc:UintVx = if(value.isInstanceOf[UintVx]) value.asInstanceOf[UintVx] else addLt(value)
}
