package progOfmacros

//import compiler._

import compiler.SpatialType._
import compiler.AST._
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.ASTB._
import compiler.ASTBfun.{Fundef3R, addRedop, inc, redop}
import compiler._
/** Contains the code of spatial macro used as a layer of  building blocks of small bits of spatial operators, compiled with optimal perf. */
object Compute {
  val concat3VDef: Fundef3[(V, B), (V, B),(V, B), (V, UI)]={
    val a = pL[V, B]("a")
    val b = pL[V, B]("b")
    val c = pL[V, B]("c")
    Fundef3("compute.concat3V", c.asInstanceOf[UintV]::b::a,a,b,c) //biarement on doit les concaténer dans cet ordre, je ne sait pas trop pourquoi
  }
  def concat3V(b0: BoolV, b1: BoolV, b2: BoolV):UintV =
    new Call3(concat3VDef, b0, b1,b2)(repr.nomLR(repr.nomV, repr.nomUI)) with UintV

  val impliqueDef: Fundef2[(V, B), (V, B), (V, B)] = {
    val a = pL[V, B]("a")
    val b = pL[V, B]("b")
    Fundef2("compute.implique", ~a | b, a, b)
  }
  def implique(b0: BoolV, b1: BoolV): BoolV = new Call2(impliqueDef, b0, b1)(repr.nomLR(repr.nomV, repr.nomB)) with BoolV

  def impluqDef[L<:Locus](implicit n:repr[L]): Fundef2[(L, B), (L, B), (L, B)] = {
    val a = pL[L, B]("a")
    val b = pL[L, B]("b")
    Fundef2("compute.impluq", ~a | b, a, b)
  }
  def impluq[L<:Locus](b0: ASTLt[L,B], b1: ASTLt[L,B])(implicit n:repr[L]): ASTLt[L,B]= new Call2(impluqDef, b0, b1) with ASTLt[L,B]
  /*

    /** Does only one or, which appear ridiciulously small for a macro, but that May avoid generating too many CaLoops */
    val orVdef: Fundef2[(V, B), (V, B), (V, B)] = {
      val b0 = pL[V, B]("b0")
      val b1 = pL[V, B]("b1")
      val r = b1 | b0
      Fundef2("orV", r, b0, b1)
    }

    def orV(b0: BoolV, b1: BoolV): BoolV = new Call2(orVdef, b0, b1) with BoolV


    val andVdef: Fundef2[(V, B), (V, B), (V, B)] = {
      val b0 = pL[V, B]("b0")
      val b1 = pL[V, B]("b1")
      val r = b1 & b0
      Fundef2("orV", r, b0, b1)
    }

    def andV(b0: BoolV, b1: BoolV): BoolV = new Call2(andVdef, b0, b1) with BoolV

    val andEdef: Fundef2[(E, B), (E, B), (E, B)] = {
      val b0 = pL[E, B]("b0")
      val b1 = pL[E, B]("b1")
      val r = b1 & b0
      Fundef2("orV", r, b0, b1)
    }

    def andE(b0: BoolE, b1: BoolE): BoolE = new Call2(andEdef, b0, b1) with BoolE


    val notEdef: Fundef1[(E, B), (E, B)] = {
      val b0 = pL[E, B]("b0")
      val r = ~b0
      Fundef1("notE", r, b0)
    }

    def notE(b0: BoolE): BoolE = new Call1(notEdef, b0) with BoolE
  */

}