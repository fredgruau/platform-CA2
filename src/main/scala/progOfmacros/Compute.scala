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