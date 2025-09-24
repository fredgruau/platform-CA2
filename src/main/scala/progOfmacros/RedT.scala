package progOfmacros

import compiler.AST.{Call1, Fundef1, pL}
import compiler.ASTBfun.{Fundef2R, Fundef2RP, andB, orB, redop}
import compiler.ASTL.{anticlock, binop, broadcast, clock, transfer}
import compiler.ASTLfun.reduce
import compiler.Circuit.iTabSymb
import compiler.SpatialType.{BoolV, BoolVe, BoolVf, UintV}
import compiler._
import progOfmacros.Topo.nbccDef
import progOfmacros.Wrapper.border

import scala.collection.immutable.HashMap
/** allows to automatically generate macro for  "Transfer-reduction" such as from Ve to Vf more generally from Zy to Zy
 * the number of operands are two
 * operands can be boolean or integers */
object RedT {
  /** cac=clock+anticlock
   * Does a binop  operation between each
   * pair of adjacent Transfer locus around a given simplicial locus S1,
   * It appliers a Clockwise, and an AntiClockwise rotation, and applies the bionop
   * This is not really a reduction, just a binop, so it does not need to define neutral elements, because
   * either an S1 site is defined and so are it transfer around,
   * or S1 is not and also so are its transfer around it.TODO remplacer par un wrapper sur RedT
   */
  def cacOld[S1 <: S, S2 <: S, S3 <: S, R <: Ring](r: Fundef2R[R], arg: ASTLt[T[S1, S2], R])(implicit m1: repr[S2], m2: repr[S1], m3: repr[S3], n: repr[R], a: AntiClock[S1, S2, S3]): ASTLt[T[S1, S3], R] = {
    binop(r, clock(arg), anticlock(arg))
  }

  def cac[S1 <: S, S2 <: S, S3 <: S, R <: Ring, P <: Ring](op2: Fundef2RP[R, P], arg: ASTLt[T[S1, S2], R])
                                                          (implicit m1: repr[S2], m2: repr[S1], m3: repr[S3], n: repr[R], p: repr[P], a: AntiClock[S1, S2, S3]): ASTLt[T[S1, S3], P] = {
    binop[T[S1, S3], R, R, P](op2, clock(arg), anticlock(arg))
  }

  def shrink(arg:BoolVe):BoolVf=cac(andB,arg)

  /*
  def cac2[S1 <: S, S2 <: S, S3 <: S, R <: Ring, P <: Ring](op2: Fundef2RP[R, P], arg: ASTLt[T[S1, S2], R], arg2: ASTLt[T[S1, S2], R])
                                                          (implicit m1: repr[S2], m2: repr[S1], m3: repr[S3], n: repr[R], p: repr[P], a: AntiClock[S1, S2, S3]): ASTLt[T[S1, S3], P] = {
    binop[T[S1, S3], R, R, P](op2, clock(arg), anticlock(arg2))
  }
*/

  /** memoizes all the already used Boolean reduction */
  private var redTmem: iTabSymb[Fundef1[(TT, Ring), (TT, Ring)]] = HashMap()

  /** how to build the name of a transfer reduction.
   * The prefix of the name (until the point) informs about the file where macro is to be stored, plus the binop
   * suffix is the operand's locus */
  private def redtfunName[S1 <: S, S2 <: S, S3 <: S, R <: Ring, P <: Ring](op: Fundef2RP[R, P])
         (implicit m: repr[S1], n: repr[S2], o: repr[S3], r: repr[R], p: repr[P], a: AntiClock[S1, S2, S3]) = {
    val y = 0
    ("" + "redT" + op.name + "." + m.name.shortName + n.name.shortName).toLowerCase
  }

  /**
   * @return computes the scala code of a whole  transfer reduction */
  def redtDirect[S1 <: S, S2 <: S, S3 <: S, R <: Ring, P <: Ring](op: Fundef2RP[R, P], arg: ASTLt[T[S1, S2], R])
       (implicit m: repr[S1], n: repr[S2], o: repr[S3], r: repr[R], p: repr[P], a: AntiClock[S1, S2, S3]): ASTLt[T[S1, S3], P] =
    cac[S1, S2, S3, R, P](op, arg)

  def redtFundef[S1 <: S, S2 <: S, S3 <: S, R <: Ring, P <: Ring](op: Fundef2RP[R, P], m: repr[S1], n: repr[S2], o: repr[S3])
        (implicit r: repr[R], p: repr[P], a: AntiClock[S1, S2, S3]): Fundef1[(T[S1, S2], R), (T[S1, S3], P)] = {
    val param = pL[T[S1, S2], R]("p" + m.name.shortName + n.name.shortName)( new repr[T[S1, S2]](T(m.name, n.name)),r)
    Fundef1(redtfunName(op)(m, n, o, r, p, a), redtDirect(op, param)(m,n,o,r,p,a), param)
  }

  def getRedTFun[S1 <: S, S2 <: S, S3 <: S, R <: Ring, P <: Ring](op: Fundef2RP[R, P], m: repr[S1], n: repr[S2], o: repr[S3])
         (implicit r: repr[R], p: repr[P], a: AntiClock[S1, S2, S3]): Fundef1[(T[S1, S2], R), (T[S1, S3], P)] = {
    val funName: String = redtfunName(op)(m, n, o, r, p, a)
    if (!redTmem.contains(funName)) {
      val fundef: Fundef1[(T[S1, S2], R), (T[S1, S3], P)] = redtFundef(op,m, n, o)( r, p, a)
      redTmem = redTmem + (funName -> fundef)
    }
    redTmem(funName).asInstanceOf[Fundef1[(T[S1, S2], R), (T[S1, S3], P)]]
  }



//LE RESTE VIRE




  /** enlarge around V, from Ve to Vf or vice versa */
  def enlarge[S1 <: S, S2 <: S](arg: ASTLt[T[V, S1], B])(implicit m1: repr[S2], m2: repr[S1], a: AntiClock[V, S1, S2]): ASTLt[T[V, S2], B] =
    cacOld[V, S1, S2, B](orB, arg)

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






  /** shrink around V, from Ve to Vf or vice versa */
  def shrink[S1 <: S, S2 <: S](arg: ASTLt[T[V, S1], B])(implicit m1: repr[S2], m2: repr[S1], a: AntiClock[V, S1, S2]): ASTLt[T[V, S2], B] =
    cacOld[V, S1, S2, B](andB, arg)

  val shrinkFEDef: Fundef1[(T[V, F], B), (T[V, E], B)] = {
    val arg = pL[T[V, F], B]("shrink")
    Fundef1("redT.shrinkFE", shrink[F, E](arg), arg)
  }

  def shrinkFE(b: BoolVf): BoolVe =
    new Call1[(T[V, F], B), (T[V, E], B)](shrinkFEDef, b) with BoolVe


  val shrinkEFDef: Fundef1[(T[V, E], B), (T[V, F], B)] = {
    val arg = pL[T[V, E], B]("shrink")
    Fundef1("redT.shrinkEF", shrink[E, F](arg), arg)
  }

  def shrinkEF(b: BoolVe): BoolVf =
    new Call1[(T[V, E], B), (T[V, F], B)](shrinkEFDef, b) with BoolVf











  def clock2(arg: BoolVe): BoolVe = clock(clock(arg)) //on peut etendre aux transfer type T[V,F], T[F,x]

  //def enlarge(arg: BoolVe): BoolVe = arg | clock2(arg)

 // def shrink(arg: BoolVe): BoolVe = arg & clock2(arg)

}
