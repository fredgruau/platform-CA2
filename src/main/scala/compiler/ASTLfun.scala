package compiler

import compiler.ASTLfun._
import ASTL._
import compiler.AST.{Fundef1, Fundef2}
import compiler.ASTB.{False, Intof, True}
import compiler.ASTBfun._
import compiler.SpatialType.IntEv

/** contains generic primitive manipulating ASTLs, without direct access to the constructors */
object ASTLfun {


  /** Allows to consider false and true as occurence of ASTLs */
  implicit def fromBool[L <: Locus](d: Boolean)(implicit m: repr[L]): ASTLt[L, B] = const(if (d == True()) True() else False())

  /** Allows to consider integers as occurence of ASTLs */
  implicit def fromInt[L <: Locus, R <: I](d: Int)(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = const(Intof(d))

  /** broadcast towards V */
  def v[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, V]], n: repr[R]): ASTLt[T[S1, V], R] = broadcast(arg); // for broadcast, we want to specify only the direction where broadcasting takes place.

  /** broadcast towards E */
  def e[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, E]], m2: repr[T[E, S1]], n: repr[R]): ASTLt[T[S1, E], R] = broadcast(arg) // this is done using three function e,v,f.

  /** broadcast towards F */
  def f[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, F]], m2: repr[T[F, S1]], n: repr[R]): ASTLt[T[S1, F], R] = broadcast(arg)

  //////// Unops //////////
  def ltSI[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): ASTLt[L, B] = unop(ASTBfun.ltSI, arg1);

  def eqSI[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): ASTLt[L, B] = unop(ASTBfun.eqSI, arg1);
  //(implicit m: repr[L], n: repr[Ro])

  /** returns the biggest signed constant on n bits, where n is adjusted at run time, when the constant is combined
   * to some other integer, using a binop. The bitifying stage   is able to extends, adding  the correct  number of bits
   */
  def maxSI[L <: Locus]()(implicit m: repr[L]): ASTLt[L, SI] = halve(-1)

  /** a vertex field get on its six edge, the six neighbor values, so that it can then reduce them. */
  def neighbors[R <: Ring](arg: ASTLt[V, R])(implicit n: repr[R]): ASTLt[T[V, E], R] = {
    //val meVois: ASTLt[T[E, V], R] = transfer(e(arg))
    transfer(sym(transfer(e(arg))))
    //  transfer(symed)
  }

  ///////////BINOP/////////////

  /** Instead of casting boolean to integer,  we define a logical and taking an int and a  bool */
  def andLB2R[L <: Locus, R <: I](arg1: ASTLt[L, B], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] =
    binop[L, B, R, R](andLBtoRUISI(arg2.ring).asInstanceOf[Fundef2[B, R, R]], arg1, arg2)


  ///////////TRIOP/////////////

  /** cond with internal test to decide wether it applies for signed int, unsigned int, or bool. */
  def cond[L <: Locus, R <: Ring](b: ASTLt[L, B], arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] =
    if (n.name.isInstanceOf[SI])
      (andLB2R[L, SI](b, arg1.asInstanceOf[ASTLt[L, SI]]) | andLB2R(~b, arg2.asInstanceOf[ASTLt[L, SI]])).asInstanceOf[ASTLt[L, R]]
    else if (n.name.isInstanceOf[UI])
      (andLB2R[L, UI](b, arg1.asInstanceOf[ASTLt[L, UI]]) | andLB2R(~b, arg2.asInstanceOf[ASTLt[L, UI]])).asInstanceOf[ASTLt[L, R]]
    else {
      assert(n.name.isInstanceOf[B])
      ((b & arg1.asInstanceOf[ASTLt[L, B]]) | (~b & arg2.asInstanceOf[ASTLt[L, B]])).asInstanceOf[ASTLt[L, R]]
    }


  /** redop is used through reduce, whichi will set undefined at the borde, to neutral element.
   * the border is introduced using implicit */
  def reduce[S1 <: S, S2 <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R])
                                         (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chipBorder[S1, S2]): ASTLt[S1, R] = {
    val neutralElt: ASTLt[T[S1, S2], R] = const[T[S1, S2], R](op._2)
    val newArg: ASTLt[T[S1, S2], R] = if (d.border == null) arg else
      cond[T[S1, S2], R](d.border, arg, neutralElt)
    redop[S1, S2, R](op, newArg)
  }


  /** reduction betwween transfer field, using clock and anticlock */
  /* def redOp2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Binop[T[S1, S2new], R, R, R] =
     Binop[T[S1, S2new], R, R, R](op._1, Clock[S1, S2, S2new, R](arg, dir = true), Clock[S1, S2, S2new, R](arg, dir = false), m, n)

   def xorR2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Binop[T[S1, S2new], R, R, R] =
     redOp2[S1, S2, S2new, R](xorRedop[R], arg)*/
}

