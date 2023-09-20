package progOfmacros

import compiler.AST.{p, _}
import compiler.ASTBfun.{andRedop, orRedop, redop, xorRedop}
import compiler.ASTL.{v, _}
import compiler.Circuit.iTabSymb
import compiler.repr.{nomB, nomCons, nomV}
import compiler.{AST, ASTLt, B, E, F, Ring, S, T, V, repr}
import progOfmacros.RedS.getFun

import scala.collection.immutable.HashMap

object RedS {
  /** memoizes all the already used Boolean reduction */
  var redSmem: iTabSymb[Fundef1[(S, B), (S, B)]] = HashMap()

  /**
   *
   * @param S1 origine simplicial type
   * @param S2 target simplicial type
   * @param r  reduction applied
   * @return function in scala which does that reduction,  memoised in redSmem
   */
  def getFun[S1 <: S, S2 <: S](r: redop[B], l: S1)(implicit m: repr[S1], n: repr[S2]): Fundef1[(S1, B), (S2, B)] = {
    val funName = redsfunName(r, l)(m, n)
    if (!redSmem.contains(funName))
      redSmem = redSmem + (funName -> redSfunDef(r, l)(m, n))
    redSmem(funName).asInstanceOf[Fundef1[(S1, B), (S2, B)]]
  }

  /** @return a call to an or reduction, exist is a more explicit name */
  def exist[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2]): ASTLt[S2, B] = {
    val f = getFun(orRedop(repr.nomB), arg.locus)(m, n)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }

  /** @return a call to an and reduction, inside is a more explicit name */
  def inside[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2]): ASTLt[S2, B] = {
    val f = getFun(andRedop(repr.nomB), arg.locus)(m, n)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }

  /** @return a call to an xor reduction, frontier is a more explicit name */
  def frontier[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2]): ASTLt[S2, B] = {
    val f = getFun(xorRedop(repr.nomB), arg.locus)(m, n)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }

  /*
  def v[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, V]], n: repr[R]): Broadcast[S1, V, R] =
  Broadcast[S1, V, R](arg, m, n); // for broadcast, we want to specify only the direction where broadcasting takes place.


  def orRdef[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] =
    Redop[S1, S2, R](orRedop[R], arg, m, n)


    case class Caall1[Ti1, To1](override val f: Fundef1[Ti1, To1], arg: AST[_ <: Ti1])(implicit n: repr[To1])

    def aaaandR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] =
      Redop[S1, S2, R](andRedop[R], arg, m, n)


    /** From a boolE, computes adjacent vertices */
    val existFun: Fundef1[(E, B), (V, B)] = {
      val e = p[E, B]("edge")
      val existV: BoolV = orRdef(transfer(v(e)))
      existV.setName("existV");
      Fundef1("existE2V", existV, e)
    }*/

}
