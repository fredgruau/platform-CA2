package progOfmacros

import compiler.{AST, ASTBfun, ASTLt, AntiClock, B, E, F, I, Locus, Ring, S, SI, T, UI, V, chip, repr}
import compiler.AST._
import compiler.ASTBfun.{Fundef2RP, andRedop, concatRedop, ltUI2, minRedop, minUI, neg, neqUI2, orRedop, orScan, orScanSI, redop, unaryToBinary2, xorRedop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.iTabSymb
import compiler.SpatialType.{BoolE, BoolV, BoolVe, BoolVf, UintE}
import compiler.repr.{nomB, nomCons, nomV}
import progOfmacros.RedS.{getRedSFun, redsDirect}
import progOfmacros.TransferToTransfer.getttFun
import progOfmacros.RedD.getRedFun
import progOfmacros.Bino.getBinFun
import progOfmacros.Cmp.getCmpFun
import progOfmacros.Cond.getCondFun
import progOfmacros.RedT.{shrinkEF, shrinkFE}
import progOfmacros.Unop.Unop.getUnopFun



/** wrapper to call  macro built on the fly, provides more explicit name and simpler syntax
 * */
object Wrapper {

  /** Wrappers for Unop macro, defined from just an unary operators  works for UI and SI */
  def segment1[L<:Locus,R<:compiler.I](arg: ASTLt[L, R])(implicit m:repr[L],ri: repr[R])={
    val f=getUnopFun(ASTBfun.orScanRight(ri),arg.locus)(m,ri,ri)
    new Call1(f,arg)(repr.nomLR(m, ri)) with ASTLt[L, R] {}  }
  /** Wrappers for comparison macro defined from binary comparators  works for UI and SI*/
    def condL[L<:Locus,R<:Ring](arg0: ASTLt[L, B], arg1: ASTLt[L, R],arg2: ASTLt[L, R])(implicit m:repr[L],ri: repr[R])={
      val f=getCondFun[L,R]( arg1.locus)(m,ri)
      new Call3(f,arg0,arg1,arg2)(repr.nomLR(m, ri)) with ASTLt[L, R] {}  }
  def ltUI2L[L<:Locus](arg1: ASTLt[L, UI],arg2: ASTLt[L, UI])(implicit m:repr[L],ri: repr[UI])={
    val f=getCmpFun[L,UI](ltUI2 , arg1.locus)(m,ri)
    new Call2(f,arg1,arg2)(repr.nomLR(m, compiler.repr.nomB)) with ASTLt[L, B] {}  }
  def neqUI2L[L<:Locus](arg1: ASTLt[L, UI],arg2: ASTLt[L, UI])(implicit m:repr[L],ri: repr[UI])={
    val f=getCmpFun[L,UI](neqUI2 , arg1.locus)(m,ri)
    new Call2(f,arg1,arg2)(repr.nomLR(m, compiler.repr.nomB)) with ASTLt[L, B] {}  }


  def not[L<:Locus,R<:Ring](arg: ASTLt[L, R])(implicit m:repr[L],r: repr[R])={
    val f:Fundef1[(L,R),(L,R)]=getUnopFun(neg[R], arg.locus)(m,r,r)
    new Call1[(L,R),(L,R)](f,arg)(repr.nomLR(m, r)) with ASTLt[L, R] {}
  }
  def unary2Bin[L<:Locus](arg: ASTLt[L, UI])(implicit m:repr[L],ri: repr[UI])={
    val f=getUnopFun(unaryToBinary2, arg.locus)(m,ri,ri)
    new Call1(f,arg)(repr.nomLR(m, compiler.repr.nomUI)) with ASTLt[L, UI] {}  }


  /** binary operators */
  def xorBin[L<:Locus,R<:Ring](arg1:ASTLt[L, R],arg2:ASTLt[L,R])(implicit m:repr[L],q:repr[R]):ASTLt[L,R]={
    val f: Fundef2[(L, R), (L, R), (L, R)] = getBinFun(xorRedop[R]._1, arg1.locus)
    new Call2[(L, R), (L, R), (L, R)] (f, arg1,arg2) with ASTLt[L, R] {}
  }

  /** contains wrapper to two families of simplicial reduction:
   * for example, with or reduction we call it "existS"
   * existS [S1,S2] does communication to go from S1 to S2
   * exist [S1,S2] does a reduction without communication to  go from T[S1,S2] to S2
   * for border, we extend the programmation to handle UintV , and not just BoolV
   *   @return a call to an or reduction, exist is a more explicit name
   *         pour defEv S1=E S2=V, the type of chipBorder is Ve therefore [S2, S1] */
  def existS[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(S1, B), (S2, B)] = getRedSFun(orRedop[B], arg.locus)(m, n, nomB, d)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }

  def transferMacro[S1 <: S, S2 <: S, R<:Ring](arg: ASTLt[T[S1,S2], R])
             (implicit m: repr[S1], n: repr[S2], r:repr[R], d: chip[S2, S1]): ASTLt[T[S2,S1], R]= {
    val f: Fundef1[(T[S1,S2], R), (T[S2,S1], R)] = getttFun(arg.locus)(m,n,r,d)
    new Call1[(T[S1,S2], R), (T[S2,S1], R)](f, arg)
      /*(repr.nomLR(n, compiler.repr.nomB))*/ with ASTLt[T[S2,S1], R] {}
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


  def borderS[S1 <: S, S2 <: S, R<:Ring](arg: ASTLt[S1, R])(implicit m: repr[S1], n: repr[S2],  r:repr[R], d: chip[S2, S1]): ASTLt[S2, R] = {
    val f: Fundef1[(S1, R), (S2, R)] = getRedSFun(xorRedop[R], arg.locus)(m, n, r, d)
    new Call1[(S1, R), (S2, R)](f, arg)(repr.nomLR(n, r)) with ASTLt[S2, R] {}
  }


  def border[S1 <: S, S2 <: S,R<:Ring](arg: ASTLt[T[S2,S1], R])(implicit m: repr[S1], n: repr[S2], r:repr[R],d: chip[S2, S1]): ASTLt[S2, R] = {
    val f: Fundef1[(T[S2,S1], R), (S2, R)] = getRedFun(xorRedop[R], m.name)(m, n, r, d)
    new Call1[(T[S2,S1], R), (S2, R)](f, arg)(repr.nomLR(n, r)) with ASTLt[S2, R] {}
  }


  def enlarge[S1 <: S, S2 <: S, S3<:S, R<:Ring](arg: ASTLt[T[S1,S2], R])
                                              (implicit m: repr[S1], n: repr[S2], o: repr[S3], r: repr[R], a: AntiClock[S1, S2, S3]): ASTLt[T[S1, S3], R]={
    val f: Fundef1[(T[S1,S2], R), (T[S1,S3], R)] = RedT.getRedTFun(orRedop[R]._1.asInstanceOf[Fundef2RP[R, R]], m,n,o)( r,r, a)
    new Call1[(T[S1,S2], R), (T[S1,S3], R)](f, arg) with ASTLt[T[S1,S3], R] {}
  }
  def shrink[S1 <: S, S2 <: S, S3<:S, R<:Ring](arg: ASTLt[T[S1,S2], R])
       (implicit m: repr[S1], n: repr[S2], o: repr[S3], r: repr[R], a: AntiClock[S1, S2, S3]): ASTLt[T[S1, S3], R]={
  val f: Fundef1[(T[S1,S2], R), (T[S1,S3], R)] = RedT.getRedTFun(andRedop[R]._1.asInstanceOf[Fundef2RP[R, R]], m,n,o)( r,r, a)
  new Call1[(T[S1,S2], R), (T[S1,S3], R)](f, arg) with ASTLt[T[S1,S3], R] {}
  }



  /** shrinks two times, boolVe to boolVe */
  def shrink1(arg:BoolVe):BoolVf=shrink[V,E,F,B](arg)
  def shrink2(arg:BoolVe):BoolVe=shrink[V,F,E,B](shrink[V,E,F,B](arg))
  def shrink3(arg:BoolVe):BoolVf= shrink[V,E,F,B](shrink2(arg))

  /** adds vertices iff continuous number of neighbors >= 3 to obtain a smoother surface */
  def smoothen(x:BoolV)={
    val brd:BoolE =Wrapper.border[V,E,B](transfer(e(x)))
    val brdVe:BoolVe=transfer(v(brd))
    x|exist(shrink2(brdVe))
  }
  def smoothen2Old(x:BoolV)={
    val brd:BoolE =Wrapper.border[V,E,B](transfer(e(x)))
    val brdVe:BoolVe=transfer(v(brd))
    x|exist(testShrink(x))
  }
  def smoothen2(x:BoolV,shrinked:BoolVf)={
    x|exist(shrinked)
  }
  def testShrink(x:BoolV)={
    val brd:BoolE =Wrapper.border[V,E,B](transfer(e(x)))
    val brdVe:BoolVe=transfer(v(brd))
    shrink3(brdVe)  }


  def leastUI[S1 <: S, S2 <: S](arg: ASTLt[S1, UI])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, UI] = {
    val f: Fundef1[(S1, UI), (S2, UI)] = getRedSFun(minRedop[UI], arg.locus)(m, n, repr.nomUI, d)
    new Call1[(S1, UI), (S2, UI)](f, arg)(repr.nomLR(n, compiler.repr.nomUI)) with ASTLt[S2, UI] {}
  }

  /** deprecated  */
  def borderSOld[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(S1, B), (S2, B)] = getRedSFun(xorRedop[B], arg.locus)(m, n, nomB, d)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }
  def borderOld[S1 <: S, S2 <: S](arg: ASTLt[T[S2,S1], B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(T[S2,S1], B), (S2, B)] = getRedFun(xorRedop[B], m.name)(m, n, nomB, d)
    new Call1[(T[S2,S1], B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }
  def borderOldish[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] =
    redsDirect(xorRedop[B], arg)

  def concatN[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chip[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(S1, B), (S2, B)] = getRedSFun(concatRedop, arg.locus)(m, n, nomB, d)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }
}


