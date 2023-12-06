package progOfmacros

import compiler.{B, S, repr}
import compiler.AST._
import compiler.ASTBfun.{andRedop, concatRedop, minRedop, minUI, orRedop, redop, xorRedop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.iTabSymb
import compiler.repr.{nomB, nomCons, nomV}
import compiler.{AST, ASTLt, B, E, F, Ring, S, SI, T, UI, V, chip, repr}
import progOfmacros.RedS.{getRedSFun, redsDirect}

object RedSwrapper {
  /** wrapper to a function built on the fly
   *
   * @return a call to an or reduction, exist is a more explicit name
   *         pour defEv S1=E S2=V, the type of chipBorder is Ve therefore [S2, S1] */
  def exist[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(S1, B), (S2, B)] = getRedSFun(orRedop[B], arg.locus)(m, n, nomB, d)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }

  def inside[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(S1, B), (S2, B)] = getRedSFun(andRedop[B], arg.locus)(m, n, nomB, d)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }


  def border[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(S1, B), (S2, B)] = getRedSFun(xorRedop[B], arg.locus)(m, n, nomB, d)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }

  def borderDirect[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] =
    redsDirect(xorRedop[B], arg)

  def concatN[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(S1, B), (S2, B)] = getRedSFun(concatRedop, arg.locus)(m, n, nomB, d)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }

  def leastUI[S1 <: S, S2 <: S](arg: ASTLt[S1, UI])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, UI] = {
    val f: Fundef1[(S1, UI), (S2, UI)] = getRedSFun(minRedop[UI], arg.locus)(m, n, repr.nomUI, d)
    new Call1[(S1, UI), (S2, UI)](f, arg)(repr.nomLR(n, compiler.repr.nomUI)) with ASTLt[S2, UI] {}
  }
}
