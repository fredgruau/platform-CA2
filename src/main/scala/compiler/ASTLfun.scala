package compiler

import compiler.ASTLfun._
import ASTL._
import compiler.AST.{Fundef1, Fundef2}
import compiler.ASTB._
import compiler.ASTBfun._
import compiler.SpatialType.IntEv

/** contains generic primitive manipulating ASTLs, without direct access to the constructors */
object ASTLfun {

  /** Allows to consider false and true as occurence of ASTLs */
  implicit def fromBool[L <: Locus](d: Boolean)(implicit m: repr[L]): ASTLt[L, B] = const(if (d) True() else False())

  /** Allows to consider integers as occurence of ASTLs */
  implicit def fromInt[L <: Locus, R <: I](d: Int)(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = const(Intof(d))


  //------------------------------------------------------comunication macro------------------------------------------------------

  /** broadcast towards V */
  def v[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, V]], n: repr[R]): ASTLt[T[S1, V], R] = broadcast(arg); // for broadcast, we want to specify only the direction where broadcasting takes place.

  /** broadcast towards E */
  def e[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, E]], m2: repr[T[E, S1]], n: repr[R]): ASTLt[T[S1, E], R] = broadcast(arg) // this is done using three function e,v,f.

  /** broadcast towards F */
  def f[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, F]], m2: repr[T[F, S1]], n: repr[R]): ASTLt[T[S1, F], R] = broadcast(arg)

  /** a vertex field get on its six edge, the six neighbor values, so that it can then reduce them. */
  def neighbors[R <: Ring](arg: ASTLt[V, R])(implicit n: repr[R]): ASTLt[T[V, E], R] = {
    //val meVois: ASTLt[T[E, V], R] = transfer(e(arg))
    transfer(sym(transfer(e(arg))))
    //  transfer(symed)
  }


  // _____________________________________________old boolean operators ___________________________________________________________________________

  /** Simple logical Or */

  /*

    def neg[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = (arg.ring match {
      case B() => unop(negB, arg.asInstanceOf[ASTLt[L, B]])(m, repr.nomB)
      case _ => unop(negSI.asInstanceOf[Fundef1[R, R]], arg)(m, n)
    }).asInstanceOf[ASTL[L, R]]
  */


  // _____________________________________________arithmetic operation ___________________________________________________________________________

  /** todo shoud work only on SI */
  def opp[L <: Locus](arg: ASTLt[L, SI])(implicit m: repr[L], n: repr[SI]): ASTLt[L, SI] = {
    unop[L, SI, SI](oppSI, arg.asInstanceOf[ASTLt[L, SI]])(m, repr.nomSI)
  }


  def inc[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = {
    if (n.name.isInstanceOf[SI]) unop[L, SI, SI](incSI, arg.asInstanceOf[ASTLt[L, SI]])(m, repr.nomSI).asInstanceOf[ASTLt[L, R]]
    else {
      assert(n.name.isInstanceOf[UI]);
      unop[L, UI, UI](incUI, arg.asInstanceOf[ASTLt[L, UI]])(m, repr.nomUI).asInstanceOf[ASTLt[L, R]]
    }
  }


  def min[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = {
    if (n.isInstanceOf[UI])
      binop(minUI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2)(m, n)
    else binop(minRelSI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2)(m, n)
  }

  // _____________________________________________arithmetic comparison ___________________________________________________________________________

  /** return true if arg1 is negative */
  def ltSI[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): ASTLt[L, B] = unop(ASTBfun.ltSI, arg1);

  /** return true if arg1 is zero */
  def eqSI[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): ASTLt[L, B] = unop(ASTBfun.eqSI, arg1);
  //(implicit m: repr[L], n: repr[Ro])

  /* def lt[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, B] = {
   if (n.isInstanceOf[SI])   binop(ASTBfun.ltSI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2)(m, n)
   else {assert(false,"comparison between unsigned int is done using directly s<");null}
 }
 */

  /** lt2 is  defined differently on SI, and UI, it uses an optimized algo for UI, that does not subtract
   * it could be called when doing comparison betwen unsigned int, by adding an extra bit
   * On UI, it is defined modulo2, so when comparing signed it, for distances, we must add a bit first. */
  def lt2[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[B]): ASTLt[L, B] =
    if (n.isInstanceOf[SI]) binop(ASTBfun.ltSI2Mod.asInstanceOf[Fundef2[R, R, B]], arg1, arg2)
    else {
      assert(n.isInstanceOf[SI])
      binop(ASTBfun.ltUI2.asInstanceOf[Fundef2[R, R, B]], arg1, arg2)
    }


  /** gt2 is called when using the comparator sign > */
  def gt2[L <: Locus](arg1: ASTLt[L, SI], arg2: ASTLt[L, SI])(implicit m: repr[L], n: repr[B]): ASTLt[L, B] =
    binop(ASTBfun.gtSI2.asInstanceOf[Fundef2[SI, SI, B]], arg1, arg2)

  //------------------------------------------------------Other Binop------------------------------------------------------

  /** Instead of casting boolean to integer,  we define a logical and taking an int and a  bool */
  def andLB2R[L <: Locus, R <: I](arg1: ASTLt[L, B], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] =
    binop[L, B, R, R](andLBtoR.asInstanceOf[Fundef2[B, R, R]], arg1, arg2)


  /*def concat2[L <: Locus, R1 <: Ring, R2 <: Ring](arg1: ASTLt[L, R1], arg2: ASTLt[L, R2])(implicit m: repr[L], n: repr[I]): ASTL[L, I] =
    Binop(concat2f.asInstanceOf[Fundef2[R1, R2, I]], arg1, arg2, m, n)
*/
  def concat2UI[L <: Locus, R1 <: Ring, R2 <: Ring](arg1: ASTLt[L, R1], arg2: ASTLt[L, R2])(implicit m: repr[L], n: repr[UI]): ASTLt[L, UI] =
    binop(concat2.asInstanceOf[Fundef2[R1, R2, UI]], arg1, arg2)

  def concat2SI[L <: Locus, R1 <: Ring, R2 <: Ring](arg1: ASTLt[L, R1], arg2: ASTLt[L, R2])(implicit m: repr[L], n: repr[SI]): ASTLt[L, SI] =
    binop(concat2.asInstanceOf[Fundef2[R1, R2, SI]], arg1, arg2)


  //------------------------------------------------------ComputingMacro------------------------------------------------------

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

  /**
   * most significant bit, interpreted as macro
   * computes an int with a single non zero bit which is the highest rank for which operand's bit is one if operand is null, output O.
   * this is an example of boolean function with a reused value: orScanRight, this implies the need of dedagification after integer unfolding
   */
  def mstb[L <: Locus, R <: I](arg1: ASTL[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = {
    val y: ASTLt[L, R] = orScanRight[L, R](arg1);
    y ^ halve(y)
  }



  //------------------------------------------------------Reduction------------------------------------------------------


  /** redop is used through reduce, which will set undefined at the border, to the  neutral element of the reduction.
   * the border is introduced using implicit */
  def reduce[S1 <: S, S2 <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R])
                                         (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chipBorder[S1, S2]): ASTLt[S1, R] = {
    val neutralElt: ASTLt[T[S1, S2], R] = const[T[S1, S2], R](op._2)
    val newArg: ASTLt[T[S1, S2], R] = if (d.border == null) arg else
      cond[T[S1, S2], R](d.border, arg, neutralElt)
    redop[S1, S2, R](op, newArg)
  }

  def orR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])
                                      (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chipBorder[S1, S2]): ASTLt[S1, R] = {
    reduce(orRedop[R], arg)
  }

  def andR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])
                                       (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chipBorder[S1, S2]): ASTLt[S1, R] = {
    reduce(andRedop[R], arg)
  }

  def xorR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])
                                       (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chipBorder[S1, S2]): ASTLt[S1, R] = {
    reduce(xorRedop[R], arg)
  }

  def minR[S1 <: S, S2 <: S, R <: I](arg: ASTLt[T[S1, S2], R])
                                    (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chipBorder[S1, S2]): ASTLt[S1, R] = {
    reduce(minRedop[R], arg)
  }

  def minSignR[S1 <: S, S2 <: S](arg: ASTLt[T[S1, S2], SI])
                                (implicit m: repr[S1], m2: repr[S2], n: repr[SI], d: chipBorder[S1, S2]): ASTLt[S1, SI] = {
    reduce(minSignRedop, arg)
  }





  /** reduction betwween transfer field, using clock and anticlock */
  /* def redOp2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Binop[T[S1, S2new], R, R, R] =
     Binop[T[S1, S2new], R, R, R](op._1, Clock[S1, S2, S2new, R](arg, dir = true), Clock[S1, S2, S2new, R](arg, dir = false), m, n)

   def xorR2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Binop[T[S1, S2new], R, R, R] =
     redOp2[S1, S2, S2new, R](xorRedop[R], arg)*/


  //------------------------------------------------------other Unop------------------------------------------------------
  //for simplification we name  the ASTL unary operator, as the unary operator defined in ASTBfun, therefore,
  // we need to distinguis both by adding ASTBfun.uItoSI

  /** when we subtract two UI we must convert to SI, by simply adding a 0 bit on the first significant bits
   * we add a "L" to make sure we can access it.
   * todo not sure about  the need to declare that implicit, also, this has already been declared */
  def uI2SIL[L <: Locus](d: ASTLt[L, UI])(implicit m: repr[L]) = unop(uI2SI, d)


  def sign[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): ASTLt[L, SI] = unop(ASTBfun.sign, arg1)

  //def castB2R[L<:Locus,R<:I]( arg: AST[L,B] )(implicit m : repr[L])  = Unop[L,B,R] (castB2RN[R],arg );

  //todo desUISIfy
  def halve[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = unop(halveBSI.asInstanceOf[Fundef1[R, R]], arg1)

  //todo desUISIfy
  def orScanRight[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = unop(orScanRightB.asInstanceOf[Fundef1[R, R]], arg1)
  //todo desUISIfy


  def neq[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, B] = unop(neqSI.asInstanceOf[Fundef1[R, B]], arg1)


  /** @param i final number of bit that we should obtain by extending
   *           extending adds a 1 if we extend a signed integers, and integers considered is negative */
  def extend[L <: Locus, R <: Ring](i: Int, arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = unop(ASTBfun.extend[R](i), arg)

  def elt[L <: Locus, R <: I](i: Int, arg: ASTLt[L, R])(implicit m: repr[L], n: repr[B]): ASTLt[L, B] =
    unop(eltUISI(arg.ring, i).asInstanceOf[Fundef1[R, B]], arg)

  /** delaying so as to obtain same radius is a special unop! */
  def increaseRadiuus[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] =
    unop(ASTBfun.increaseRadius2[R], arg)

}

