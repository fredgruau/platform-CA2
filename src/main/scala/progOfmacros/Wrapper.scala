package progOfmacros

import compiler.{AST, ASTLt, B, E, F, Locus, Ring, S, SI, T, UI, V, chip, repr}
import compiler.AST._
import compiler.ASTBfun.{andRedop, concatRedop, minRedop, minUI, orRedop, redop, xorRedop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.iTabSymb
import compiler.repr.{nomB, nomCons, nomV}
import progOfmacros.RedS.{  getRedSFun, redsDirect}
import progOfmacros.RedD.{ getRedFun}
import progOfmacros.Bino.{ getBinFun}


/** contains wrapper to two families of simplicial reduction:
 * for example, with or reduction we call it "existS"
 * existS [S1,S2] does communication to go from S1 to S2
 * exist [S1,S2] does a reduction without communication to  go from T[S1,S2] to S2
 * */
object Wrapper {
  /** wrapper to a function built on the fly
   *
   * @return a call to an or reduction, exist is a more explicit name
   *         pour defEv S1=E S2=V, the type of chipBorder is Ve therefore [S2, S1] */
  def existS[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(S1, B), (S2, B)] = getRedSFun(orRedop[B], arg.locus)(m, n, nomB, d)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }

  def orR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])
         (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chip[S1, S2]): ASTLt[S1, R] = {
    reduce(orRedop[R], arg)
  }


  def exist[S1 <: S, S2 <: S](arg: ASTLt[T[S2,S1], B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(T[S2,S1], B), (S2, B)] = getRedFun(orRedop[B], m.name)(m, n, nomB, d)
    new Call1[(T[S2,S1], B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }

  def insideS[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(S1, B), (S2, B)] = getRedSFun(andRedop[B], arg.locus)(m, n, nomB, d)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }

  def inside[S1 <: S, S2 <: S](arg: ASTLt[T[S2,S1], B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(T[S2,S1], B), (S2, B)] = getRedFun(andRedop[B], m.name)(m, n, nomB, d)
    new Call1[(T[S2,S1], B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }

  def xorBin[L<:Locus,R<:Ring](arg1:ASTLt[L, R],arg2:ASTLt[L,R])(implicit m:repr[L],q:repr[R]):ASTLt[L,R]={
    val f: Fundef2[(L, R), (L, R), (L, R)] = getBinFun(xorRedop[R]._1, arg1.locus)
    new Call2[(L, R), (L, R), (L, R)] (f, arg1,arg2) with ASTLt[L, R] {}
  }

  def borderS[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(S1, B), (S2, B)] = getRedSFun(xorRedop[B], arg.locus)(m, n, nomB, d)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }

  def border[S1 <: S, S2 <: S](arg: ASTLt[T[S2,S1], B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(T[S2,S1], B), (S2, B)] = getRedFun(xorRedop[B], m.name)(m, n, nomB, d)
    new Call1[(T[S2,S1], B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }
  def borderOld[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] =
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
