package progOfmacros

import compiler.AST.{Call1, Fundef1, pL}
import compiler.ASTBfun.{Fundef2R, orB}
import compiler.ASTL.{anticlock, binop, clock}
import compiler.SpatialType.{BoolVe, BoolVf, UintV}
import compiler._
import progOfmacros.Topo.nbccDef

object RedT {

  /** cac=clock+anticlock
   * Does a binop  operation between the two Transfer locus around a given simplicial locus S1,
   * by doing a Clockwise, and an AntiClockwise rotation, and applying the bionop
   * This is not really a reduction, just a binop, so it does not need to define neutral elements, because
   * either an S1 site is defined and so are it transfer around,
   * or S1 is not and also so are its transfer around it.
   */
  def cac[S1 <: S, S2 <: S, S3 <: S, R <: Ring](r: Fundef2R[R], arg: ASTLt[T[S1, S2], R])
                                               (implicit m1: repr[S2], m2: repr[S1], m3: repr[S3], n: repr[R], a: AntiClock[S1, S2, S3]): ASTLt[T[S1, S3], R] = {
    binop(r, clock(arg), anticlock(arg))
  }

  /** enlarge around V, from Ve to Vf or vice versa */
  def enlarge[S1 <: S, S2 <: S](arg: ASTLt[T[V, S1], B])(implicit m1: repr[S2], m2: repr[S1], a: AntiClock[V, S1, S2]): ASTLt[T[V, S2], B] = cac[V, S1, S2, B](orB, arg)

  val enlargeFEDef: Fundef1[(T[V, F], B), (T[V, E], B)] = {
    val arg = pL[T[V, F], B]("enlarge")
    Fundef1("redT.enlargeFE", enlarge[F, E](arg), arg)
  }

  def enlargeFE(b: BoolVf): BoolVe =
    new Call1[(T[V, F], B), (T[V, E], B)](enlargeFEDef, b) with BoolVe


  val enlargeEFDef: Fundef1[(T[V, E], B), (T[V, F], B)] = {
    val arg = pL[T[V, E], B]("enlarge")
    Fundef1("redT.enlargeEF", enlarge[E, F](arg), arg)
  }

  def enlargeEF(b: BoolVe): BoolVf =
    new Call1[(T[V, E], B), (T[V, F], B)](enlargeEFDef, b) with BoolVf

  def clock2(arg: BoolVe): BoolVe = clock(clock(arg)) //on peut etendre aux transfer type T[V,F], T[F,x]

  //def enlarge(arg: BoolVe): BoolVe = arg | clock2(arg)

  def shrink(arg: BoolVe): BoolVe = arg & clock2(arg)

}
