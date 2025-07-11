package compiler

import compiler.ASTLfun._
import ASTL._
import compiler.AST.{Fundef1, Fundef2}
import compiler.ASTB._
import compiler.ASTBfun._
import compiler.SpatialType._
import compiler.ASTLfun.carryV
import progOfmacros.Wrapper._
import sdn.Globals.root4naming

/** contains generic building block manipulating ASTLs, without direct access to the constructors
 * they are not implemented in macro, because they are used by macro.
 * we  have communication, and computation as presented in the spatial type papers, and others */
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
  def f[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, F]], m2: repr[T[F, S1]], n: repr[R]): ASTLt[T[S1, F], R] = broadcast[S1, F, R](arg)

  /** a vertex field get on its six edge, the six neighbor values, so that it can then reduce them. */
  def neighbors[R <: Ring](arg: ASTLt[V, R])(implicit n: repr[R]): ASTLt[T[V, E], R] = {
    //val meVois: ASTLt[T[E, V], R] = transfer(e(arg))
    transfer(sym(transfer(e(arg))))
    //  transfer(symed)
  }

  /** go through the edge to the other neighbor Ve->Ev->Ev->Ve*/
  //def toNeighb(arg: BoolVe): BoolVe = transfer(sym(transfer(arg)))

  /** either Ef to Vf or vice versa, depending on arg */
  def apex[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, F], R])
                                       (implicit m1: repr[S1], m2: repr[S2], n: repr[R], s: CentralSym[S1, F, S2]): ASTLt[T[S2, F], R] = {
    transfer(sym(transfer(arg)))
  }

  /**
   *
   * @param is represent blobs
   * @return a BoolVf where each neigbor blob component will be represented by a single bit out of the six
   *         this is a version minimizing the number of gates (only 18) but more difficult to figure out on the border,
   *         and not reusable when the frontier is encoded as a boolE
   */
  def oneToOneOptimized(is: BoolV): BoolVf = {
    val brd: BoolE = borderS(is)
    val brdIn: BoolVe = transfer(v(brd)) & e(is) //builds a Ve true if on the border, and also on the filled side. this transfer needs an implicit
    val cbrdin: BoolFv = transfer(clock(brdIn)) //opposite the edge
    val ccbrdin: BoolVf = transfer(clock(clock(cbrdin))) //we are there
    ccbrdin
  }


  /**
   * Does two consecutive exists,
   *
   * @param brd
   * @return boolE x true  iff among the five edges withing the rhombus centered on x , one is true for brd,
   */
  def rhombusExist(brd: BoolE): BoolE = {
    val brdF: BoolF = existS[E, F](brd)
    existS[F, E](brdF) //second use of brdE, check that there is a totally empty rhombus between two blobs
  }

  // _____________________________________________arithmetic operation ___________________________________________________________________________

  /** todo shoud work only on SI */
  def opp[L <: Locus](arg: ASTLt[L, SI])(implicit m: repr[L], n: repr[SI]): ASTLt[L, SI] = {
    unop[L, SI, SI](oppSI, arg)(m, repr.nomSI)
  }




  def min[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = {
    if (n.isInstanceOf[UI])
      binop(minUI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2)(m, n)
    else assert(false);
    null // we cannot take the min modulo. binop(minRelSI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2)(m, n)
  }

  // _____________________________________________arithmetic comparison ___________________________________________________________________________

  /** defined on integers, return true if arg1 is negative */
  def ltSI[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): ASTLt[L, B] = unop(ASTBfun.ltSI, arg1);

  /** return true if arg1 is zero, */
  def eq0[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, B] = unop(ASTBfun.eq, arg1);
  /** return true if arg1 is zero, */
  def isneg[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L], n: repr[SI]): ASTLt[L, B] = unop(ASTBfun.isneg, arg1);

/** returns true if argument is not zero, it makes an or reduction on the bits. */
  def neq[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, B] = unop(ASTBfun.neq, arg1);
  def allOne[L <: Locus](arg1: ASTLt[L, UI])(implicit m: repr[L]): ASTLt[L, B] = unop(ASTBfun.allOneUI, arg1);



  /** lt2 is  defined differently on SI, and UI, it uses an optimized algo for UI, that does not subtract
   * it could be called when doing comparison betwen unsigned int, by adding an extra bit
   * On UI, it is defined modulo2, so when comparing signed it, for distances, we must add a bit first. */
  def lt2[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, B] = {
    if (!n.name.isInstanceOf[UI]) //we never have to compare signed int, what we do is  take the sign.
      assert(false)
    binop(ASTBfun.ltUI2.asInstanceOf[Fundef2[R, R, B]], arg1, arg2)
    }

 /** workl for signed or unsigned int */
  def neq2[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, B] = {
    binop(ASTBfun.neqUI2.asInstanceOf[Fundef2[R, R, B]], arg1, arg2)
  }



  /** when finalized, shoud return true if arg1 < arg2 or arg1= arg2 and  randbit*/
  def le2Rand[R <: Ring](arg1: ASTLt[V, R], arg2: ASTLt[V, R])(implicit  n: repr[R]): BoolV = {
    if (!n.name.isInstanceOf[UI]) //we never have to compare signed int, what we do is  take the sign.
      assert(false)
    lt2(arg1,arg2) //| (~neq2(arg1,arg2)) // & root4naming.addRandBit().asInstanceOf[BoolV])
  }


  /** gt2 is simply lt2 inverting the argument order */
  def gt2[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[B]): ASTLt[L, B] = {
    assert(n.isInstanceOf[UI]) //we never have to compare signed int, what we do is  take the sign.
    binop(ASTBfun.ltUI2.asInstanceOf[Fundef2[R, R, B]], arg2, arg1)
  }
  //------------------------------------------------------Other Binop------------------------------------------------------

  /** Instead of casting boolean to integer,  we define a logical and taking an int and a  bool */
  def andLB2R[L <: Locus, R <: Ring](arg1: ASTLt[L, B], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] =
    binop[L, B, R, R](andLBtoR.asInstanceOf[Fundef2[B, R, R]], arg1, arg2)

  /** concat two bits into an unsigned int, or one bit and an unsigned int into an unsigned int, or two unsigned int into an unsigned int */
  def concat2UI[L <: Locus, R1 <: Ring, R2 <: Ring](arg1: ASTLt[L, R1], arg2: ASTLt[L, R2])(implicit m: repr[L], n: repr[UI]): ASTLt[L, UI] = {
    assert(arg1.ring == B() || arg1.ring == UI())
    binop(ASTBfun.concat2UI.asInstanceOf[Fundef2[R1, R2, UI]], arg1, arg2)
  }

  //------------------------------------------------------ComputingMacro with more that two inputs or outputs------------------------------------------------------

  /** we use macro for computation on three arguments, in order not to have to introduce "triop" but use several binop */
  def cond[L <: Locus, R <: Ring](b: ASTLt[L, B], arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] =
    andLB2R(b, arg1) | andLB2R(~b, arg2)

  def imply[L <: Locus](a: ASTLt[L, B], b: ASTLt[L, B])(implicit m: repr[L]): ASTLt[L, B] =  ~a | b



  /** carryV is not written as a macro to avoid generating too many macro */
  def carryV(b0: BoolV, b1: BoolV, b2: BoolV): BoolV = (b0 & b1) | (b2 & (b0 | b1))

  /** does on two bits, the same of max 3 non zero bits, non adjacents, distributed over 6 bits */
  def sum3V(b0: BoolV, b1: BoolV, b2: BoolV): UintV = (b0 ^ b1 ^ b2) :: carryV(b0, b1, b2)

  /**
   * most significant bit, interpreted as macro
   * computes an int with a single non zero bit which is the highest rank for which operand's bit is one if operand is null, output O.
   * this is an example of boolean function with a reused value: orScanRight, this implies the need of dedagification after integer unfolding
   */
  def mstb[L <: Locus, R <: I](arg1: ASTL[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = {
    val y: ASTLt[L, R] = orScanRight[L, R](arg1);
    ~halve(y) ^ y //it may bug because embrouille avec deux scan.
  }

  def unary(b0: BoolV, b1: BoolV): List[BoolV] = List(b0 & b1, ~b0 & b1, b0 & ~b1, ~b0 & ~b1)


  //------------------------------------------------------Reduction------------------------------------------------------


  /** redop is used through reduce, which will set undefined at the border, to the  neutral element of the reduction.
   * the border is introduced using implicit */
  def reduce[S1 <: S, S2 <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R])
                                         (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chip[S1, S2]): ASTLt[S1, R] = {
    val neutralElt: ASTLt[T[S1, S2], R] = const[T[S1, S2], R](op._2)
    val newArg: ASTLt[T[S1, S2], R] = if (d.df == null || true) arg else //enlever le || true pour re-avoir l'usage des def.
      cond[T[S1, S2], R](d.df, arg, neutralElt)
    redop[S1, S2, R](op, newArg)
  }

  /** when reducing towards an edge, there is only two values to combine */
  def ltUiEdge [ S2 <: S](arg: ASTLt[T[E, S2], UI])(implicit m2: repr[S2], d:chip[E,S2]): ASTLt[E, B] = {
    binopEdge(ltUI2,arg)
    //reduce(ltUiRedop, arg).asInstanceOf[BoolE]
  }
  def eqUiEdge [ S2 <: S](arg: ASTLt[T[E, S2], UI])(implicit m2: repr[S2], d:chip[E,S2]): ASTLt[E, B] = {
    binopEdge(eqUI2,arg)
    //reduce(ltUiRedop, arg).asInstanceOf[BoolE]
  }

  def firstEdge[ S2 <: S](arg: ASTLt[T[E, S2], UI])(implicit m2: repr[S2],r:repr[UI], d:chip[E,S2]): ASTLt[E, UI] = {
    binopEdge(firstOfTwoUI,arg)
    //reduce(ltUiRedop, arg).asInstanceOf[BoolE]
  }


  def orR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])
                                      (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chip[S1, S2]): ASTLt[S1, R] = {
    reduce(orRedop[R], arg)
  }

  def orR2[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])
                                       (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chip[S1, S2]): ASTLt[S1, R] = {
    reduce(or2Redop[R], arg)
  }


  /* def concatR[S1 <: S, S2 <: S](arg: ASTLt[T[S1, S2], B])(implicit m: repr[S1], n: repr[UI]): ASTLt[S1, UI] =
     RedopConcat[S1, S2](arg, m, n)
 */

  /** We had to use a reduction, bool,bool->boole which forces us to retrieve a bool, but we need a UI so we do a cast */
  def concatR[S1 <: S, S2 <: S, R<:Ring](arg: ASTLt[T[S1, S2], R])
                               (implicit m: repr[S1], m2: repr[S2]): ASTLt[S1, UI] = {
    val res = redop[S1, S2, UI](concatRedop, arg.asInstanceOf[ASTLt[T[S1, S2], UI]])
    res.asInstanceOf[ASTLt[S1, UI]]
  }

  def concatRold[S1 <: S, S2 <: S](arg: ASTLt[T[S1, S2], B])
                               (implicit m: repr[S1], m2: repr[S2]): ASTLt[S1, UI] = {
    val res = redop[S1, S2, UI](concatRedop, arg.asInstanceOf[ASTLt[T[S1, S2], UI]])
    res.asInstanceOf[ASTLt[S1, UI]]
  }

  /*  def castUI[L<:Locus](arg: ASTLt[L, B]):ASTLt[L, UI]=
      {val res=arg.asInstanceOf[ASTLt[L, UI] ]
        res.mym=repr(arg.locus,UI()).asInstanceOf[repr[(L,UI)]]
        res
      }*/
  def andR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])
                                       (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chip[S1, S2]): ASTLt[S1, R] = {
    reduce(andRedop[R], arg)
  }

  def xorR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])
                                       (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chip[S1, S2]): ASTLt[S1, R] = {
    reduce(xorRedop[R], arg)
  }

  def minR[S1 <: S, S2 <: S, R <: I](arg: ASTLt[T[S1, S2], R])
                                    (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chip[S1, S2]): ASTLt[S1, R] = {
    reduce(minRedop[R], arg)
  }

  def minSignR[S1 <: S, S2 <: S](arg: ASTLt[T[S1, S2], SI])
                                (implicit m: repr[S1], m2: repr[S2], n: repr[SI], d: chip[S1, S2]): ASTLt[S1, SI] = {
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
  def b2SIL[L <: Locus](d: ASTLt[L, B])(implicit m: repr[L]) = unop(b2SI, d)



  def sign[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): ASTLt[L, SI] = unop(ASTBfun.sign, arg1)

  //def castB2R[L<:Locus,R<:I]( arg: AST[L,B] )(implicit m : repr[L])  = Unop[L,B,R] (castB2RN[R],arg );

  //todo desUISIfy
  def halve[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = unop(halveB, arg1)

  //todo desUISIfy
  def orScanRight[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = unop(ASTBfun.orScanRight, arg1)
  //todo desUISIfy

  def inc[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = unop(ASTBfun.inc, arg1)
  //todo desUISIfy


  /** @param i final number of bit that we should obtain by extending
   *           extending adds a 1 if we extend a signed integers, and integers considered is negative */
  def extend[L <: Locus, R <: Ring](i: Int, arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = unop(ASTBfun.extend[R](i), arg)

  def elt[L <: Locus, R <: I](i: Int, arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, B] =
    unop(ASTBfun.elt(i), arg)

  /** delaying so as to obtain same radius is a special unop! */
  def increaseRadiuus[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] =
    unop(ASTBfun.increaseRadius2[R], arg)

}

