package compiler

import AST.{p, _}
import ASTB.{tm1, _}
import ASTBfun.{orRedop, _}
import ASTL.{Redop, Send, _}
import dataStruc.Align2._
import Constraint._
import Circuit.{iTabSymb2, _}
import repr._
import dataStruc.Dag
import dataStruc.DagNode._

import scala.annotation.unused
import scala.collection.{mutable, _}
import scala.reflect.ClassTag
import scala.language.implicitConversions

/**
 * At some point, we decided to store the type information for each distinct constructor, in order to have direct access to this info
 * when copying the constructor,
 * this enabled to enforce the covariance in L:Locus and R:Ring, which was intuitive and would therefore facilitate things later on.
 * but then we abandonned it, so we could come back to previous setting where type was not stored, and copied in case class copying (see ASTBs).
 */
object ASTL {
  val u = 1

  private[ASTL] case class Coonst[L <: Locus, R <: Ring](cte: ASTBt[R], m: repr[L], n: repr[R]) extends ASTL[L, R]()(repr.nomLR(m, n)) with EmptyBag[AST[_]]

  private[ASTL]
  final case class Broadcast[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[S1, R], m: repr[T[S1, S2]], n: repr[R])
    extends ASTL[T[S1, S2], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]

  /** a bit more subtle than broadcast  */
  private[ASTL] final case class Send[S1 <: S, S2 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, S2]], n: repr[R])
    extends ASTL[T[S1, S2], R]() with Neton[AST[_]]

  private[ASTL] final case class Transfer[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R], m: repr[T[S2, S1]], n: repr[R])
    extends ASTL[T[S2, S1], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]

  /** Unop is not final, because we can add operators < */
  private[ASTL] case class Unop[L <: Locus, R1 <: Ring, R2 <: Ring](op: Fundef1[R1, R2], arg: ASTLt[L, R1], m: repr[L], n: repr[R2])
    extends ASTL[L, R2]()(repr.nomLR(m, n)) with Singleton[AST[_]]

  private[ASTL] final case class Binop[L <: Locus, R1 <: Ring, R2 <: Ring, R3 <: Ring](
                                                                                        op: Fundef2[R1, R2, R3], arg: ASTLt[L, R1], arg2: ASTLt[L, R2], m: repr[L], n: repr[R3])
    extends ASTL[L, R3]()(repr.nomLR(m, n)) with Doubleton[AST[_]]


  /**
   *
   * @param op
   * @param arg
   * @param m : implicit used to compute the locus and scala type
   *          made a lot of effort to make it covariant, but that seems useless, in fact.
   *          I've put the type locus + ring as part of  the case construct's fields, so that it becomes very easy to copy
   * @param n
   * @tparam S1 towards wich we reduce
   * @tparam S2
   * @tparam R
   */
  private[ASTL] final case class Redop[S1 <: S, S2 <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R], m: repr[S1], n: repr[R])
    extends ASTL[S1, R]()(repr.nomLR(m, n)) with Singleton[AST[_]] {
    /** used to compute the expression being reduced.  */
    override def redExpr: List[AST[_]] = List(arg)
  }

  def concatR[S1 <: S, S2 <: S](arg: ASTLt[T[S1, S2], B])(implicit m: repr[S1], n: repr[UI]): RedopConcat[S1, S2] =
    RedopConcat[S1, S2](arg, m, n)

  /** the concat reduction has a different signature it takes a bool transfer, and produces an unsigned int. n=UI */
  private[ASTL] final case class RedopConcat[S1 <: S, S2 <: S](arg: ASTLt[T[S1, S2], B], m: repr[S1], n: repr[UI])
    extends ASTL[S1, UI]()(repr.nomLR(m, n)) with Singleton[AST[_]] {
    /** used to compute the expression being reduced.  */
    override def redExpr: List[AST[_]] = List(arg)
  }

  private[ASTL] final case class Clock[S1 <: S, S2 <: S, S3 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R], dir: Boolean)(implicit m: repr[T[S1, S3]], n: repr[R])
    extends ASTL[T[S1, S3], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]

  /** central symmetry, used on vertices */
  private[ASTL] final case class Sym[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R], m: repr[T[S1, S2new]], t: CentralSym[S2, S1, S2new], n: repr[R])
    extends ASTL[T[S1, S2new], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]

  /** delaying so as to obtain same radius is a special unop! */


  /** Field which has a value both  at time t, and t+1 */
  trait Strate[L <: Locus, R <: Ring] {
    val pred: ASTLt[L, R];
    val next: ASTLt[L, R]
  }

  def rotR[T](seq: Seq[T], i: Int): Seq[T] = {
    val size = seq.size
    seq.drop(size - (i % size)) ++ seq.take(size - (i % size))
  }

  def rotL[T](a: Array[T])(implicit m: ClassTag[T]): Array[T] = a.drop(1) :+ a(0)

  def rotR[T](a: Array[T])(implicit m: ClassTag[T]): Array[T] = a(a.length - 1) +: a.take(a.length - 1)

  //def rotR[T](a: Array[T], jump: Int)(implicit m: ClassTag[T]): Array[T] = Array.concat(a.drop(jump), a.take(jump))

  def rot[T](a: Array[T], dir: Boolean)(implicit m: ClassTag[T]): Array[T] = if (dir) rotR(a) else rotL(a) //dir=True correspond to trigonometric order
  def rotPerm(dec: Int): Array[Int] = {
    val r = new Array[Int](6);
    for (i <- 0 to 5) r(i) = (i + dec) % 6;
    r
  }

  def composeAll(p: Array[Int], t: iTabSymb[Array[Int]]): Map[String, Array[Int]] = t.map { case (k, v) => k -> compose(p, v) }

  def composeAll2(p: Array[Int], t: iTabSymb2[Array[Int]]): iTabSymb2[Array[Int]] = t.map { case (k, v) => k -> compose(p, v) }


  /** Allows to consider false and true as occurence of ASTLs */
  implicit def fromBool[L <: Locus](d: Boolean)(implicit m: repr[L]): ASTLt[L, B] = Coonst(if (d == True()) True() else False(), m, repr.nomB)

  /** Allows to consider integers as occurence of ASTLs */
  implicit def fromInt[L <: Locus, R <: I](d: Int)(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = Coonst(Intof(d)(n), m, n)

  /** when we subtract two UI we automatically convert to SI, bysimply adding a 0 bit on the first significant bits */
  implicit def uItoSIL[L <: Locus](d: ASTLt[L, UI])(implicit m: repr[L]) =
    new Unop[L, UI, SI](ASTBfun.uItoSIdef, d, m, repr.nomSI) //adds the comparison operators, which requires signed bit because we take the opposite


  type ASTLg = ASTLt[_ <: Locus, _ <: Ring]
  type rewriteASTLt[L <: Locus, R <: Ring] = ASTLt[L, R] => ASTLt[L, R]
  //type bij2[L <: Locus, R <: Ring] = ASTL[L, R] => ASTL[L, R]

  /** ***************the wrapper *******************/

  def const[L <: Locus, R <: Ring](cte: ASTBt[R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = Coonst(cte, m, n)

  def sym[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], t: CentralSym[S2, S1, S2new], n: repr[R]): Sym[S1, S2, S2new, R] = Sym(arg, m, t, n)

  def v[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, V]], n: repr[R]): Broadcast[S1, V, R] = Broadcast[S1, V, R](arg, m, n); // for broadcast, we want to specify only the direction where broadcasting takes place.
  def e[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, E]], m2: repr[T[E, S1]], n: repr[R]): Broadcast[S1, E, R] = Broadcast[S1, E, R](arg, m, n); // this is done using three function e,v,f.
  def f[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, F]], m2: repr[T[F, S1]], n: repr[R]): Broadcast[S1, F, R] = Broadcast[S1, F, R](arg, m, n)

  def clock[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Clock[S1, S2, S2new, R] = Clock[S1, S2, S2new, R](arg, dir = true)

  def anticlock[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Clock[S1, S2, S2new, R] = Clock[S1, S2, S2new, R](arg, dir = false)


  //Builds a transfer, just like v,e,f, however specify a diffent Simplicial field for each component; used for substraction.
  def sendv[S1 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, V]], n: repr[R]): Send[S1, V, R] = {
    assert(args.length == 6 / args.head.locus.density);
    Send[S1, V, R](args);
  } //TODO check the length of args
  def sende[S1 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, E]], n: repr[R]) = Send[S1, E, R](args);

  //  def sendf[S1 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, F]], n: repr[R]) = Send[S1, F, R](args) ;

  //def castB2R[L<:Locus,R<:I]( arg: AST[L,B] )(implicit m : repr[L])  = Unop[L,B,R] (castB2RN[R],arg );
  def transfer[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S2, S1]], n: repr[R]):
  ASTLt[T[S2, S1], R] = Transfer(arg, m, n)


  //def v[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, V]], n: repr[R]): Broadcast[S1, V, R] = Broadcast[S1, V, R](arg, m, n); // for broadcast, we want to specify only the direction where broadcasting takes place.

  def broadcast[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, S2]], n: repr[R]): ASTLt[T[S1, S2], R] =
    Broadcast[S1, S2, R](arg, m, n) //step 1 is broadcast

  //def unop[L <: Locus, Ri <: Ring, Ro <: Ring](f: Fundef1[Ri, Ro])(implicit m: repr[L], n: repr[Ro]) = (arg1: ASTLt[L, Ri]) => Unop[L, Ri, Ro](f, arg1, m, n)
  def sign[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): ASTLt[L, SI] = Unop[L, SI, SI](ASTBfun.sign, arg1, m, nomSI)


  //todo desUISIfy
  def halve[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = Unop[L, R, R](
    halveB.asInstanceOf[Fundef1[R, R]], arg1, m, n)

  //todo desUISIfy
  def orScanRight[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, R, R] = Unop[L, R, R](halveB.asInstanceOf[Fundef1[R, R]], arg1, m, n)

  //todo desUISIfy
  def lt[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): Unop[L, SI, B] =
    Unop[L, SI, B](ltSI1.asInstanceOf[Fundef1[SI, B]], arg1, m, repr.nomB); //-1 will be taken modulo nbit.

  /* def ltUI2[L <: Locus](arg1: ASTLt[L, UI], arg2: ASTLt[L, UI])(implicit m: repr[L], n: repr[B]): ASTL[L, B] =
     Binop(ASTBfun.ltUI2.asInstanceOf[Fundef2[UI, UI, B]], arg1, arg2, m, n)
 */
  def lt2[L <: Locus](arg1: ASTLt[L, SI], arg2: ASTLt[L, SI])(implicit m: repr[L], n: repr[B]): ASTL[L, B] =
    Binop(ASTBfun.ltSI2.asInstanceOf[Fundef2[SI, SI, B]], arg1, arg2, m, n)

  def gt2[L <: Locus](arg1: ASTLt[L, SI], arg2: ASTLt[L, SI])(implicit m: repr[L], n: repr[B]): ASTL[L, B] =
    Binop(ASTBfun.gtSI2.asInstanceOf[Fundef2[SI, SI, B]], arg1, arg2, m, n)


  //todo desUISIfy
  def notNull[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, R, B] = Unop[L, R, B](neqSI.asInstanceOf[Fundef1[R, B]], arg1, m, repr.nomB)

  /** Instead of casting boolean to integer,  we define a logical and taking an int and a  bool */
  def andLB2R[L <: Locus, R <: I](arg1: ASTLt[L, B], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Binop[L, B, R, R] =
    Binop[L, B, R, R](andLBtoRUISI(arg2.ring).asInstanceOf[Fundef2[B, R, R]], arg1, arg2, m, n)

  /*def concat2[L <: Locus, R1 <: Ring, R2 <: Ring](arg1: ASTLt[L, R1], arg2: ASTLt[L, R2])(implicit m: repr[L], n: repr[I]): ASTL[L, I] =
    Binop(concat2f.asInstanceOf[Fundef2[R1, R2, I]], arg1, arg2, m, n)
*/
  def concat2UI[L <: Locus, R1 <: Ring, R2 <: Ring](arg1: ASTLt[L, R1], arg2: ASTLt[L, R2])(implicit m: repr[L], n: repr[UI]): ASTL[L, UI] =
    Binop(concat2f.asInstanceOf[Fundef2[R1, R2, UI]], arg1, arg2, m, n)

  def concat2SI[L <: Locus, R1 <: Ring, R2 <: Ring](arg1: ASTLt[L, R1], arg2: ASTLt[L, R2])(implicit m: repr[L], n: repr[SI]): ASTL[L, SI] =
    Binop(concat2f.asInstanceOf[Fundef2[R1, R2, SI]], arg1, arg2, m, n)

  /** @param i final number of bit */
  def extend[L <: Locus, R <: Ring](i: Int, arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, R, R] =
    Unop[L, R, R](ASTBfun.extend[R](i).asInstanceOf[Fundef1[R, R]], arg, m, n)

  def elem[L <: Locus, R <: I](i: Int, arg: ASTLt[L, R])(implicit m: repr[L], n: repr[B]): Unop[L, R, B] =
    Unop[L, R, B](eltUISI(arg.ring, i).asInstanceOf[Fundef1[R, B]], arg, m, n)

  /** binop that implements a delay */
  def increaseRadiuus[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, R, R] = {
    val op = ASTBfun.increaseRadius2[R]
    val lll = Unop[L, R, R](op, arg, m, n)
    lll
  }
  //{ ASTL.Unop(opp.asInstanceOf[Fundef1[R, SI]], this, m, repr.nomSI) }

  //def concat[L <: Locus, R <: I](arg1: Seq[ASTLtrait[L, R]])(implicit m: repr[L], n: repr[R]) = Multop2[L, R, R](concatN, arg1,m,n);
  // def orR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]) = Redop[S1, S2, R]((orI.asInstanceOf[Fundef2[R, R, R]], False[R]), arg, m, n);

  /**
   * reduction operator
   */

  /**
   * version obsolete car il faudrait faire un match pour chaque op, ce qu'on peut eviter.
   *
   * @param op  reduction operator
   * @param arg arguement being reduced
   * @param m   : implicit used to compute the locus
   * @param n   implicit used to compute the scalar type
   * @tparam S1 main spatial locus
   * @tparam S2 secondary spatial locus
   * @tparam R  scalar type, boolean or int for example
   *            Like redop excep it does a preliminary binop
   *            with defVE which is true when the value is defined.
   *            When it is not defined, the binop result shoudl take the neutral value (O for Or, 1 for and...)
   */
  def reduceBool[S1 <: S, S2 <: S](op: redop[B], arg: ASTLt[T[S1, S2], B]) //S1=V
                                  (implicit m: repr[S1], m2: repr[S2], n: repr[B], d: chipBorder[S1, S2]): Redop[S1, S2, B] = {
    val newArg: ASTLt[T[S1, S2], B] = if (d.border == null) arg //d.border null means we do not need it.
    else op match {
      case (orb, _) => //todo inclure to les transfer locus, pas seulement Ve
        and[T[S1, S2], B](d.border, arg)(nomT(m, m2), nomB) //met a zero is pas border
    }
    Redop[S1, S2, B](op, newArg, m, n)
  }


  /** version that works both for reduction with booleans or reduction with integers, such as min, or addOnes.
   * for the moment it seems boolean is the most important, so we consider only this one */
  def reduce[S1 <: S, S2 <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R])
                                         (implicit m: repr[S1], m2: repr[S2], n: repr[R], d: chipBorder[S1, S2]): ASTL[S1, R] = {
    val neutralElt: ASTL[T[S1, S2], R] = const[T[S1, S2], R](op._2)
    val newArg: ASTLt[T[S1, S2], R] = if (d.border == null) arg else
      cond[T[S1, S2], R](d.border, arg, neutralElt)
    Redop[S1, S2, R](op, newArg, m, n)
  }

  /** or Reduction which works both for boolean and integers, but does not use the border so it is obsolote */
  def orR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] = {
    assert(false) //we do not want to use this.
    Redop[S1, S2, R](orRedop[R], arg, m, n)
  }

  /** or reduction processing the border, should be extended to include integers */
  def orRB[S1 <: S, S2 <: S](arg: ASTLt[T[S1, S2], B])(implicit m: repr[S1], n: repr[S2], d: chipBorder[S1, S2]): Redop[S1, S2, B] =
    reduceBool[S1, S2](orRedop[B], arg)(m, n, nomB, d)


  /** version of or reduction taking into account undefined value on chip's border using an implici d:chipBorder */
  def orRdef[S1 <: S, S2 <: S](arg: ASTLt[T[S1, S2], B])
                              (implicit m: repr[S1], m2: repr[S2], d: chipBorder[S1, S2]): Redop[S1, S2, B] =
    reduceBool[S1, S2](orRedop[B], arg)

  def andRdef[S1 <: S, S2 <: S](arg: ASTLt[T[S1, S2], B])
                               (implicit m: repr[S1], m2: repr[S2], d: chipBorder[S1, S2]): Redop[S1, S2, B] =
    reduceBool[S1, S2](andRedop[B], arg)

  def andR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] =
    Redop[S1, S2, R](andRedop[R], arg, m, n)

  def xorR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] =
    Redop[S1, S2, R](xorRedop[R], arg, m, n)


  /**
   * reduction operator, which use the static defVe, defVf
   */
  def orRdef[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] =
    Redop[S1, S2, R](orRedop[R], arg, m, n)




  /** reduction betwween transfer field, using clock and anticlock */
  def redOp2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Binop[T[S1, S2new], R, R, R] =
    Binop[T[S1, S2new], R, R, R](op._1, Clock[S1, S2, S2new, R](arg, dir = true), Clock[S1, S2, S2new, R](arg, dir = false), m, n)

  def xorR2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Binop[T[S1, S2new], R, R, R] =
    redOp2[S1, S2, S2new, R](xorRedop[R], arg)

  def subESI[S2 <: S](arg: ASTLt[T[E, S2], SI])(implicit m: repr[E]): ASTLt[E, SI] =
    Redop[E, S2, SI]((subSI, Intof[SI](0)), arg, m, repr.nomSI).asInstanceOf[ASTLt[E, SI]]

  def addESI[S2 <: S](arg: ASTLt[T[E, S2], SI])(implicit m: repr[E]): ASTLt[E, SI] =
    Redop[E, S2, SI]((addSI, Intof[SI](0)), arg, m, repr.nomSI).asInstanceOf[ASTLt[E, SI]]


  /** minR has two implementations depending if the integers to be compared are signed or unsigned. */
  def minR[S1 <: S, S2 <: S, R <: I](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): ASTLt[S1, R] =
    if (arg.ring == SI()) Redop[S1, S2, SI]((minSI, Intof[SI](0)), arg.asInstanceOf[ASTLt[T[S1, S2], SI]], m, repr.nomSI).asInstanceOf[ASTLt[S1, R]]
    else Redop[S1, S2, UI]((minUI, Intof[UI](0)), arg.asInstanceOf[ASTLt[T[S1, S2], UI]], m, repr.nomUI).asInstanceOf[ASTLt[S1, R]]

  /** delayedL reprograms delayed, in order to add the trait ASTLt[L, R] */
  def delayedL[L <: Locus, R <: Ring](_arg: => ASTLt[L, R])(implicit m: repr[(L, R)]): ASTLt[L, R] = {
    lazy val delayed = _arg;
    new Delayed[(L, R)](() => delayed) with ASTLt[L, R]
  }


  def condOld[L <: Locus, R <: I](b: ASTLt[L, B], arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] =
    andLB2R[L, R](b, arg1) | andLB2R(~b, arg2)

  /** cond behavees differently for boolean, we are obliged to rewrite it. */
  /*  def condB[L <: Locus](b: ASTLt[L, B], arg1: ASTLt[L, B], arg2: ASTLt[L,B])(implicit m: repr[L]): ASTL[L, B] = {
      val res=(b & arg1 )| (~b & arg2)
      res
    }*/


  /** we designed a cond that makes an internal test to decide wether it applies for int or for bool. */
  def cond[L <: Locus, R <: Ring](b: ASTLt[L, B], arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] =
    if (n.name.isInstanceOf[SI])
      (andLB2R[L, SI](b, arg1.asInstanceOf[ASTLt[L, SI]]) | andLB2R(~b, arg2.asInstanceOf[ASTLt[L, SI]])).asInstanceOf[ASTLt[L, R]]
    else
      ((b & arg1.asInstanceOf[ASTLt[L, B]]) | (~b & arg2.asInstanceOf[ASTLt[L, B]])).asInstanceOf[ASTLt[L, R]]

  /**
   * computes an int with a single non zero bit which is the highest rank for which operand's bit is one if operand is null, output O.
   * this is an example of boolean function with a reused value: orScanRight.
   */
  def mstb[L <: Locus, R <: I](arg1: ASTL[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = {
    val y: ASTL[L, R] = orScanRight[L, R](arg1);
    y ^ halve(y)
  }


  // _____________________________________________arithmetic comparison ___________________________________________________________________________


  // _____________________________________________boolean operators ___________________________________________________________________________
  /** Simple logical Or */
  def or[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg1.ring match {
    case B() => Binop(orB, arg1.asInstanceOf[ASTLt[L, B]], arg2.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case _ => Binop(orUISI(arg1.ring).asInstanceOf[Fundef2[R, R, R]], arg1, arg2, m, n)
  }).asInstanceOf[ASTL[L, R]]

  /** Simple logical And */
  def and[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg1.ring match {
    case B() => Binop(andB, arg1.asInstanceOf[ASTLt[L, B]], arg2.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case _ => Binop(andUISI(arg1.ring).asInstanceOf[Fundef2[R, R, R]], arg1, arg2, m, n)
  }).asInstanceOf[ASTL[L, R]]

  /** Simple logical Xor */
  def xor[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg1.ring match {

    case B() => Binop(xorB, arg1.asInstanceOf[ASTLt[L, B]], arg2.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case _ => Binop(xorUISI(arg1.ring).asInstanceOf[Fundef2[R, R, R]], arg1, arg2, m, n)
  }).asInstanceOf[ASTL[L, R]]

  def neg[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg.ring match {
    case B() => Unop(negB, arg.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case _ => Unop(negSI.asInstanceOf[Fundef1[R, R]], arg, m, n)
  }).asInstanceOf[ASTL[L, R]]

  def id[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg.ring match {
    case B() => Unop(identityB, arg.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case UI() => Unop(identityUI.asInstanceOf[Fundef1[R, R]], arg, m, n)
    case SI() => Unop(identitySI.asInstanceOf[Fundef1[R, R]], arg, m, n)
  }).asInstanceOf[ASTL[L, R]]


  def opp[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, SI, SI] =
    Unop[L, SI, SI](oppSI, arg.asInstanceOf[ASTLt[L, SI]], m, repr.nomSI)

  def inc[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, SI, SI] =
    Unop[L, SI, SI](incSI, arg.asInstanceOf[ASTLt[L, SI]], m, repr.nomSI)


  /** uses a fixed val addUISI, and let the compiler believe that this val has the appropriate expected  type R=UI or R=SI  */
  def add[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = {
    Binop(addUISI(n.name).asInstanceOf[Fundef2[R, R, R]], arg1, arg2, m, n)
  }


  type ASTLtG = ASTLt[_ <: Locus, _ <: Ring]
  type IntV = ASTLt[V, SI];
  type IntE = ASTLt[E, SI];
  type IntF = ASTLt[F, SI]
  type IntvE = ASTLt[T[E, V], SI];
  type InteV = ASTLt[T[V, E], SI]
  type IntvF = ASTLt[T[F, V], SI];
  type IntfV = ASTLt[T[V, F], SI]
  type IntfE = ASTLt[T[E, F], SI];
  type InteF = ASTLt[T[F, E], SI]
  type UintV = ASTLt[V, UI];
  type UintE = ASTLt[E, UI];
  type UintF = ASTLt[F, UI]
  type UintvE = ASTLt[T[E, V], UI];
  type UinteV = ASTLt[T[V, E], UI]
  type UintvF = ASTLt[T[F, V], UI];
  type UintfV = ASTLt[T[V, F], UI]
  type UintfE = ASTLt[T[E, F], UI];
  type UinteF = ASTLt[T[F, E], UI]
  type BoolV = ASTLt[V, B];
  type BoolE = ASTLt[E, B];
  type BoolF = ASTLt[F, B]
  type BooleV = ASTLt[T[V, E], B];
  type BoolvE = ASTLt[T[E, V], B]
  type BoolvF = ASTLt[T[F, V], B];
  type BoolfV = ASTLt[T[V, F], B]
  type BoolfE = ASTLt[T[E, F], B];
  type BooleF = ASTLt[T[F, E], B]
  //  def neg2[L <: Locus, R <: Ring](arg: AST2[L, R])(implicit m: repr[L], n: repr[R]) = Unop[L, R, R](negN[R], arg);
  // implicit def fromAST2[L<:Locus,R<:Ring](x:AST2[L, R]):ASTL[L,R]=x.asInstanceOf[ASTL[L,R]
}

/**
 * AST of spatial type
 *
 * @tparam L : the locus in V,E or F   *  @tparam R: the  type   *  @constructor
 * @param m : implicit used to compute the locus and scala type
 *          made a lot of effort to make it covariant, but that seems useless, in fact.
 *          I've put the type locus + ring as part of  the case construct's fields, so that it becomes very easy to copy
 */
sealed abstract class ASTL[L <: Locus, R <: Ring]()(implicit m: repr[(L, R)]) extends ASTLt[L, R] {
  override def isRedop =
    this.asInstanceOf[ASTL[_, _]] match {
      case Redop(_, _, _, _) => true
      case _ => false
    }

  def opRedop =
    this.asInstanceOf[ASTL[_, _]] match {
      case Redop(op, _, _, _) => op
      case _ => throw new Exception("tried to take op of nonredop")
    }

  override def toString: String =
    this.asInstanceOf[ASTL[_, _]] match {
      //  case Layer(s, _)                 => "Layer " + this.name + ":" + locus.toString.charAt(0) + "-" + ring.toString.charAt(0)
      case Binop(op, _, _, _, _) => op.name
      case Coonst(cte, _, _) => "Const" + cte.toString + locus.toString.charAt(0) + "_" + ring.toString.substring(0, ring.toString.length() - 2);

      //  case Multop(op, args,_,_)      => op.toString
      case Unop(op, _, _, _) => op.name
      case Redop(op: (Fundef2R[Ring], ASTBt[Ring]), _, _, _) => "red" + op._1.name
      case RedopConcat(_, _, _) => "redConcat"
      case Clock(_, dir) => if (dir) "clock" else "anticlock"
      case e@Broadcast(_, _, _) => "Broadcast" + ("" + (e.locus.asInstanceOf[T[_, _]] match {
        case T(_, y) => y
      })).charAt(0)
      case e@Send(_) => "Send" + ("" + (e.locus.asInstanceOf[T[_, _]] match {
        case T(_, y) => y
      })).charAt(0)
      case Transfer(_, _, _) => "Transfer"
      case Sym(_, _, _, _) => "sym "
    }

  /**
   * @param id rewritting procedure
   * @return ASTL obtained by applying the rewriting recursively
   *         No  override, because name is distinct from AST's propagate */
  def propagateASTL(id: rewriteASTLt[L, R]): ASTL[L, R] = {
    def id2[L3 <: Locus, R3 <: Ring]: rewriteASTLt[L3, R3] = d => id(d.asInstanceOf[ASTLt[L, R]]).asInstanceOf[ASTLt[L3, R3]] //introduit des variables libres
    val newD = this.asInstanceOf[ASTLg] match {
      case e: EmptyBag[_] => e
      case e@Broadcast(a, _, _) => e.copy(arg = id2(a))
      case e@Send(a) => e.copy(args = a.map(id2))(lpart(e.mym), rpart(e.mym))
      case e@Transfer(a, _, _) => e.copy(arg = id2(a))
      case e@Unop(_, a, _, _) => e.copy(arg = id2(a))
      case e@Binop(_, a, a2, _, _) => e.copy(arg = id2(a), arg2 = id2(a2))
      case e@Redop(_, a, _, _) => e.copy(arg = id2(a))
      case e@RedopConcat(a, _, _) => e.copy(arg = id2(a))
      case e@Clock(a, _) => e.copy(arg = id2(a))(lpart(e.mym), rpart(e.mym))
      case e@Sym(a, _, _, _) => e.copy(arg = id2(a))
    };
    newD.setName(this.name);
    newD.asInstanceOf[ASTL[L, R]]
  }

  /**
   * @param cur        The current programm
   * @param ASTbitSize Stores number of bits of sub expression.
   * @param newtSymb   The symbol table with number of bits of parameters and progressively upadated with variables
   * @return Expression rewritten so as to include Extend, when binop operators are used,
   *         and one of the two operands has not enough bits.
   *
   */
  override def bitIfyAndExtend(cur: DataProg[InfoType[_]], ASTbitSize: AstMap[Int], newtSymb: TabSymb[InfoNbit[_]]): ASTLt[L, R] = {
    val emptyAstMapInt = immutable.HashMap.empty[AST[_], Int] //stores the bit number of an ASTB expression
    /** collect the bit size that  the spatial param and then non spatial operators should have. */
    val paramBitIncrease = mutable.HashMap.empty[String, Int]

    val result = this match {
      case Binop(op, a, a2, l2, r2) => //BINOP needs more work, because it triggers possible insertion of  "extend";
        var anew = a.bitIfyAndExtend(cur, ASTbitSize, newtSymb); //process recursively subtree
        var a2new = a2.bitIfyAndExtend(cur, ASTbitSize, newtSymb) //process recursively subtree
        val nbitASTBParam = emptyAstMapInt + (op.p1 -> ASTbitSize(anew)) + (op.p2 -> ASTbitSize(a2new)) // bit size  of the parameters of the boolean function
        val nbitResult: Int = ASTB.nbitExpAndParam(nbitASTBParam, op.arg, paramBitIncrease) //retrieves the number of bit computed from the call to the ASTB fonction
        if (paramBitIncrease.contains(op.p1.nameP)) //check if first ASTL param is desired to be "extended"
        anew = anew.extendMe(paramBitIncrease(op.p1.nameP)) //extends parameters used in the expression
        // of the first effective parameter if the first ASTB param is desired to be extended
        if (paramBitIncrease.contains(op.p2.nameP)) //check if second ASTL param shoudl be "extended"
        a2new = a2new.extendMe(paramBitIncrease(op.p2.nameP)) //same thing for second effective parameter
        val newthis = Binop(op, anew, a2new, l2, r2)
        ASTbitSize += newthis -> nbitResult //Store the bitsize of the Binop
        newthis
      case _ => //in all the other cases, no change is done on the AST, only  expASTLbitSize is updated.
        val newthis = this.propagateASTL((d: ASTLt[L, R]) => d.bitIfyAndExtend(cur, ASTbitSize, newtSymb))

        def argBitSize() = ASTbitSize(newthis.asInstanceOf[Singleton[AST[_]]].arg) //bit size of the arg if singleton

        ASTbitSize += newthis -> (newthis.asInstanceOf[ASTL[_, _]] match {
          // case l:Layer[_,_] =>  l.nbit
          case Coonst(cte, _, _) => ASTB.nbitExpAndParam(emptyAstMapInt, cte, paramBitIncrease)
          case Unop(op, _, _, _) => ASTB.nbitExpAndParam(emptyAstMapInt + (op.p1 -> argBitSize()), op.arg, paramBitIncrease)
          case Redop(_, _, _, _) | Clock(_, _) | Transfer(_, _, _) | Broadcast(_, _, _) | Sym(_, _, _, _) => argBitSize() //bit size equals bit size of arg
          case Send(_) => ASTbitSize(newthis.asInstanceOf[Neton[AST[_]]].args.head)
          case RedopConcat(exp, _, _) => this.locus.fanout //for the concat redop, the number of bit must take into account the arity (2,3, or 6)

        })
        newthis
    };
    result.setName(this.name);
    result
  }

  /**
   * @return true if the expression contains  only 1-concatenation -2-elt or 3-Broadcast
   *         indeed, those operators can be handled at the level of main instead of macro
   **/
  override def justConcatsorBroadcast: Boolean = this.asInstanceOf[ASTLg] match {
    case Unop(Fundef1(namef, _, _), arg, _, _) =>
      if (namef.startsWith("elt"))
        arg.justConcatsorBroadcast
      else false
    case Binop(Fundef2("concat", _, _, _), arg, arg2, _, _) =>
      arg.justConcatsorBroadcast && arg2.justConcatsorBroadcast
    case RedopConcat(arg, _, _) => arg.justConcatsorBroadcast
    case Broadcast(arg, _, _) => arg.justConcatsorBroadcast
    case _ => super.justConcatsorBroadcast
  }

  def redOpSeq(m: Machine, zones: Dag[Zone], tZone: Map[String, Zone]) = this.asInstanceOf[ASTLg] match {
    case Redop(op, a, _, _) =>
      val expUnfolded = a.unfoldTransfer(m)
      val u = 0
  }

  override def unfoldSimplic(m: Machine): ArrAst = {
    val r = rpart(mym.asInstanceOf[repr[(L, R)]])
    val s = this.locus.asInstanceOf[S]
    this.asInstanceOf[ASTLg] match {
      case Coonst(cte, _, _) => Array.fill(s.sufx.length)(cte)
      case Broadcast(_, _, _) => throw new RuntimeException("Broadcast creates   a transfer type")
      case Send(_) => throw new RuntimeException("Broadcast creates   a transfer type")
      case Transfer(_, _, _) => throw new RuntimeException("Transfer creates   a transfer type")
      case Unop(op, a, _, _) =>
        if (op.name.equals("increaseRadius")) //we add the tm1s early so as to be able to remove them early
        // a.unfoldTransfer(m).map(_.map(x => tm1[R](x.asInstanceOf[ASTBt[R]])(n.asInstanceOf[repr[R]]).asInstanceOf[ASTBg]))
          a.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m).map(
            (x => tm1[R](x.asInstanceOf[ASTBt[R]])(r).asInstanceOf[ASTBg]))
        else
          a.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m).map(
        new Call1(op.asInstanceOf[Fundef1[Any, R]], _)(r) with ASTBt[R].asInstanceOf[ASTBg])
      case Binop(op, a, a2, _, _) => a.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m).zip(a2.unfoldSimplic(m)).map({
        case (c, c2) => new Call2(op.asInstanceOf[Fundef2[Any, Any, R]], c, c2)(r) with ASTBt[R].asInstanceOf[ASTBg]
      })
      case Redop(op, a, _, _) =>

        /** creates a binary tree of several call to opred       */
        def reduceEncapsulated(as: Array[ASTBt[R]], opred: redop[R]) =
          as.toList.tail.foldLeft(as(0))(new Call2(opred._1, _, _)(r) with ASTBt[R])

        a.unfoldTransfer(m).map((x: ArrAst) =>
          reduceEncapsulated(x.asInstanceOf[Array[ASTBt[R]]], op.asInstanceOf[redop[R]])).asInstanceOf[ArrAst]
      case RedopConcat(a, _, _) =>
        def reduceConcatEncapsulated(as: Array[ASTBt[B]]): ASTBt[UI] =
          as.toList.tail.foldLeft(as(0).asInstanceOf[ASTBt[UI]])(new Concat2[UI, B, UI](_, _))

        a.unfoldTransfer(m).map((x: ArrAst) =>
          reduceConcatEncapsulated(x.asInstanceOf[Array[ASTBt[B]]])).asInstanceOf[ArrAst]
      case Clock(_, _) => throw new RuntimeException("Clock creates    a transfer type")

      case Sym(_, _, _, _) => throw new RuntimeException("Sym creates  a transfer type")
    }
    //read and Call treated in ASTLt.

  }

  override def unfoldTransfer(m: Machine): ArrArrAstBg = {
    val T(s1, des) = this.locus;
    val rr = this.ring
    val suf = this.locus.sufx
    val l2 = suf.length
    this.asInstanceOf[ASTLg] match {
      case Coonst(cte, _, _) => Array.fill(s1.sufx.length, l2)(cte)
      case Broadcast(a, _, _) =>
        a.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m).map(Array.fill(l2)(_))
      case Send(a) =>
        if (a.length != l2) throw new RuntimeException("incorrect number of arguments for send")
        a.toArray.map(_.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m)).transpose
      case Transfer(a, _, _) =>
        val u = 0
        val res = m(des, s1, a.unfoldTransfer(m))
        res
      case Unop(op, a, _, n) => //todo faire le cas simplicial
        if (op.name.equals("increaseRadius")) //we add the tm1s early so as to be able to remove them early
          a.unfoldTransfer(m).map(_.map(x => tm1[R](x.asInstanceOf[ASTBt[R]])(n.asInstanceOf[repr[R]]).asInstanceOf[ASTBg]))

        else a.unfoldTransfer(m).map(_.map(new Call1(op.asInstanceOf[Fundef1[Any, R]], _)(n.asInstanceOf[repr[R]]) with ASTBt[R].asInstanceOf[ASTBg]))
      case Binop(op, a, a2, _, n) => a.unfoldTransfer(m).zip(a2.unfoldTransfer(m)).map({
        case (b, b2) => b.zip(b2).map({
          case (c, c2) =>
            new Call2(op.asInstanceOf[Fundef2[Any, Any, R]], c, c2)(n.asInstanceOf[repr[R]]) with ASTBt[R].asInstanceOf[ASTBg]
        })
      })
      case Redop(_, _, _, _) => throw new RuntimeException("Reduces create a simplicial type, not a transfer type")
      case Clock(a, dir) =>
        val T(_, src) = a.locus
        val trigo = !dir
        val atr = a.unfoldTransfer(m)
        if ((src < des) ^ dir) atr else atr.map(rot(_, trigo))
      case Sym(a, _, _, _) =>
        val T(s1, src) = a.locus;
        val atr: Array[Array[ASTBg]] = a.unfoldTransfer(m).map(rotR(_));
        val res = s1 match {
          case V() => atr.map(rotR(_)).map(rotR(_)) //throw new RuntimeException("sym not defined on V in the general case")
          case E() => atr // la composée de deux rotation est une rotation simple qui est aussi une permutation pour E.
          case F() => if (src < des) atr else atr.map(rotR(_)) //we follow trigonometric, the composition of tree anticlock  must add one rotation, if not(src<des).
        }
        res
      //read and Call treated in ASTLt.
    }
  }

  def shouldAffect: Boolean = this match {
    case Redop(_, _, _, _) => true
    case Binop(_, a1, a2, _, _) => a1.isInstanceOf[ASTL.Clock[_, _, _, _]] || a2.isInstanceOf[ASTL.Clock[_, _, _, _]] || a1.isInstanceOf[ASTL.Sym[_, _, _, _]] || a2.isInstanceOf[ASTL.Sym[_, _, _, _]] //that's an overkill, unnecessary introduced variables will have to be removed
    case _ => false
  }

  /**
   * @param r stores results consisting of alignement, shifted instructions, and generated constraints
   * @return tree with some id being replaced by shifted version,
   *         cycle constraint, instruction setting the shifted version, alignement with respect to used variables.
   */
  override def align(r: Result, tt: TabSymb[InfoNbit[_]]): ASTLt[L, R] = {
    val newExp = this.asInstanceOf[ASTLg] match { //read and Call treated in ASTLt.
      case Coonst(_, _, _) => this
      case e@Broadcast(arg, _, _) => val newArg = arg.align(r, tt);
        r.algn = r.algn.map { case (k, v) => k -> arg.locus.proj };
        e.copy(arg = newArg)


      case e@Send(args) => val newArgs = args.map(_.align(r, tt)) //collects results in $r
        r.algn = r.algn.map { case (k, v) => k -> args.head.locus.proj } //does not depend on v, because v is constant
        e.copy(args = newArgs)(lpart(e.mym), rpart(e.mym))
      case e@Transfer(arg, _, _) =>
        val T(s1, s2) = arg.locus;
        val t = hexPermut((s1, s2));
        val newArg = arg.align(r, tt);
        r.c = permute(r.c, t, e.locus);
        r.algn = composeAll2(t, r.algn)
        e.copy(arg = newArg)
      case e@Unop(_, arg, _, _) => e.copy(arg = arg.align(r, tt))
      case e@Binop(_, arg, arg2, _, _) =>
        var newArg = arg.align(r, tt)
        val algn: Map[String, Array[Int]] = r.algn
        var newArg2 = arg2.align(r, tt)
        val k = algn.keys.toSet.intersect(r.algn.keys.toSet);
        assert(k.size <= 1, " more than one to aligne !")
        if (k.nonEmpty && !(algn(k.head) sameElements r.algn(k.head))) {
          //k is the aux defined by an instr which will have to use two registers.
          val nome: String = k.head //here we assume that there is a single input variable
          val perm = compose(invert(algn(nome)), r.algn(nome))
          val shiftedE = "shift" + nome
          r.c = intersect(r.c, Some(Cycle(perm, locus.asInstanceOf[TT])))

          //  val shiftInstr = ShiftInstr(shiftedE, e, perm)
          //val repr = arg.mym.asInstanceOf[repr[(L, R)]]
          val repr = new repr(tt(nome).t) // asInstanceOf[repr[(L, R)]]
          val read = new Read(nome)(repr) with ASTLt[L, R] //not used at the end!

          //  val shiftInstr = Affect(shiftedE, arg) //we shift the clock in order to obtain the right correspondance
          val shiftInstr = Affect(shiftedE, read) //we shift the clock in order to obtain the right correspondance
          // between shif and shifted
          //TODO le alignperm de shiftInstr on le fait ensuite!
          //    shiftInstr.alignPerm=perm
          r.si += nome -> shiftInstr
          r.algn += shiftedE -> algn(nome)
          //newArg = newArg.replaceBy(nome, shiftedE)
          newArg2 = newArg2.replaceBy(nome, shiftedE)
        }
        e.copy(arg = newArg, arg2 = newArg2)
      case e@Redop(_, arg, _, _) => e.copy(arg = arg.align(r, tt))
      case e@Clock(arg, dir) =>
        val newArg = arg.align(r, tt)
        val T(_, des) = this.locus;
        val T(_, src) = arg.locus;
        val trigo = !dir;
        val atr = rotPerm(if (trigo) 1 else 5) //faudrait vérifier is c'est pas le contraire
        if ((src < des) ^ dir) {
          r.c = permute(r.c, atr, e.locus);
          r.algn = composeAll2(atr, r.algn)
        }
        e.copy(arg = newArg)(lpart(e.mym), rpart(e.mym))
      case e@Sym(arg, _, _, _) => val newArg = arg.align(r, tt)
        val T(_, des) = this.locus;
        val T(s1, src) = arg.locus;
        val atr = rotPerm(s1 match { case E() => 1 case F() => if (src < des) 1 else 2 case V() => 3 });
        r.c = permute(r.c, atr, e.locus);
        r.algn = composeAll2(atr, r.algn)
        e.copy(arg = newArg)

    }
    newExp.asInstanceOf[ASTL[L, R]]
  }


  /**
   *
   * @param r for computation of all the radius, collect the radius of identifier , plus a modifier making it precise for Edge and Face wether
   *          they are perimeter or radial
   * @param t symbol table to be updated for paramR() to paramRR(Int) where int indicate the radius of result param
   * @return radius and modifier of expression
   */
  override def radiusify2(r: TabSymb[Int], t: TabSymb[InfoNbit[_]]): Int = {
    def increaseRadius(rad: Int, src: Locus, target: Locus): Int = {
      val newRadius = (src, target) match {
        case (V(), _) | (E(), F()) => rad + 1
        case _ => rad
      }
      assert(newRadius < 2) // we have to do  another communication between radius=1 and radius=-2
      newRadius
    }

    this.asInstanceOf[ASTLg] match {
      case Coonst(_, _, _) => -1000 //radius is arbitrary
      case Transfer(arg, _, _) => {
        val rad = arg.radiusify2(r, t)
        val T(src, target) = arg.locus //we get the source and target locus knowing that arg is a transfer locus
        increaseRadius(rad, src, target)
      }
      case Binop(_, arg, arg2, _, _) =>
        val r1 = arg.radiusify2(r, t)
        val r2 = arg2.radiusify2(r, t)
        assert(r1 == r2 || r1 < 0 || r2 < 0, "binop should processe variables of identical index i") //todo introduce delays
        math.max(r1, r2)

      case Unop(op, arg, _, _) =>
        arg.radiusify2(r, t) +
          (if (op.name == "increaseRadius")
            1
          else 0) //ca ne change pas
      case Broadcast(arg, _, _) => arg.radiusify2(r, t) //ca ne change pas
      case Redop(_, arg, _, _) => arg.radiusify2(r, t) //ca ne change pas
      case RedopConcat(arg, _, _) => arg.radiusify2(r, t) //ca ne change pas
      case Clock(arg, _) => arg.radiusify2(r, t) //ca ne change pas
      case Send(args) => args(0).radiusify2(r, t) //ca ne change pas
      case Sym(arg, _, _, _) => arg.radiusify2(r, t) //ca ne change pas
    }

  }

  override def radiusify3(r: TabSymb[Int], t: TabSymb[InfoNbit[_]]): (Int, ASTLt[L, R]) = {
    def increaseRadius(rad: Int, src: Locus, target: Locus): Int = {
      val newRadius = (src, target) match {
        case (V(), _) | (E(), F()) => rad + 1
        case _ => rad
      }
      assert(newRadius < 2) // we have to do  another communication between radius=1 and radius=-2
      newRadius
    }

    this.asInstanceOf[ASTLg] match {
      case trans@Transfer(arg, m, n) => {
        val (rad, newArg) = arg.radiusify3(r, t)
        val T(src, target) = arg.locus //we get the source and target locus knowing that arg is a transfer locus
        (increaseRadius(rad, src, target), trans.copy(arg = newArg).asInstanceOf[ASTL[L, R]])
      }
      case binop@Binop(_, arg, arg2, _, _) =>
        var (r1, newArg) = arg.radiusify3(r, t)
        var (r2, newArg2) = arg2.radiusify3(r, t)
        assert(r1 == r2 || r1 < 0 || r2 < 0 || Math.abs(r1 - r2) == 1, "binop should processe variables of near identical index i") //todo introduce delays)
        if (r1 < r2 && r1 >= 0) //negative radius means constant
          newArg = increaseRadiuus(newArg)(new repr(newArg.locus), new repr(newArg.ring)) //we augment radius of arg by delaying it
        else if (r2 < r1 && r2 >= 0) //negative radius means constant
          newArg2 = increaseRadiuus(newArg2)(new repr(newArg2.locus), new repr(newArg2.ring)) //we augment radius of arg2 by delaying it
        // if (r1 < r2) for (i <- 0 until r2 - r1) //arg=tm1(arg)
        (math.max(r1, r2), binop.copy(arg = newArg, arg2 = newArg2).asInstanceOf[ASTL[L, R]])
      case Coonst(_, _, _) => (-1000, this) //negative radius means arbitrary radius,
      case u@Unop(op, arg, _, _) =>
        var (rad, newArg) = arg.radiusify3(r, t)
        rad = rad + (if (op.name == "increaseRadius") 1 else 0)
        (rad, u.copy(arg = newArg).asInstanceOf[ASTL[L, R]])
      //for other cases we do nothing
      case b@Broadcast(arg, _, _) => val (rad, newArg) = arg.radiusify3(r, t); (rad, b.copy(arg = newArg).asInstanceOf[ASTL[L, R]])
      case b@Redop(_, arg, _, _) => val (rad, newArg) = arg.radiusify3(r, t); (rad, b.copy(arg = newArg).asInstanceOf[ASTL[L, R]])
      case b@RedopConcat(arg, _, _) => val (rad, newArg) = arg.radiusify3(r, t); (rad, b.copy(arg = newArg).asInstanceOf[ASTL[L, R]])
      // case b@Clock(arg, _) =>  val (rad,newArg) = arg.radiusify3(r, t);(rad,b.copy(arg=newArg).asInstanceOf[ASTL[L,R]])
      case b@Sym(arg, _, _, _) => val (rad, newArg) = arg.radiusify3(r, t); (rad, b.copy(arg = newArg).asInstanceOf[ASTL[L, R]])
      case b@Send(args) => val radNewArgs = args.map(_.radiusify3(r, t));
        val newRad = radNewArgs.map(_._1).reduce(Math.max(_, _)) //todo  check that all the radius are the same.
        val newb = b.copy(args = radNewArgs.map(_._2))(lpart(b.mym), rpart(b.mym))
        (newRad, newb.asInstanceOf[ASTL[L, R]])

    }

  }

  override def radiusify(r: TabSymb[(Int, Option[Modifier])], t: TabSymb[InfoNbit[_]]): (Int, Option[Modifier]) = {

    /**
     * t
     *
     * @param rad    radius
     * @param m      modifier: Perimeter or Radial
     * @param src    locus of  origin
     * @param target locus of  destination
     * @return transcribes the automata presented in the article,
     *         so as to possibly increase the radius, and update the locus modifier
     *         it seems that now it is obsolete, we replaced radius by radius2
     */
    def increaseRadiusObsolete(rad: Int, m: Option[Modifier], src: Locus, target: Locus): (Int, Option[Modifier]) = {
      val newRadius = (src, m, target) match {
        case (E(), Some(Perimeter()), F()) | // case where the radius does not increase
             (F(), Some(Radial()), E()) | // case where the radius does not increase
             (E(), Some(Radial()), V()) // case where the radius does not increase
        => rad
        case _ => rad + 1
      }
      val newModifier: Option[Modifier] = (src, target) match {
        case (E(), F()) => m
        case (F(), E()) => Modifier.invertModifier(m)
        case (V(), _) => Some(Perimeter())
        case (_, V()) => None
      }
      (newRadius, newModifier)
    }

    this.asInstanceOf[ASTLg] match {
      case Coonst(_, _, _) => startRadius(locus)
      case Transfer(arg, _, _) => {
        val (rad, m) = arg.radiusify(r, t)
        val T(src, target) = arg.locus //we get the source and target locus knowing that arg is a transfer locus
        increaseRadiusObsolete(rad, m, src, target)
      }
      case Binop(_, arg, arg2, _, _) => val (r1, t1) = arg.radiusify(r, t)
        val (r2, t2) = arg2.radiusify(r, t)
        assert(r1 == r2 && t1 == t2, "binop should processe variables of identical radius")
        (r1, t1)
      case Unop(_, arg, _, _) => arg.radiusify(r, t) //ca ne change pas
      case Broadcast(arg, _, _) => arg.radiusify(r, t) //ca ne change pas
      case Redop(_, arg, _, _) => arg.radiusify(r, t) //ca ne change pas
      case RedopConcat(arg, _, _) => arg.radiusify(r, t) //ca ne change pas
      case Clock(arg, _) => arg.radiusify(r, t) //ca ne change pas
      case Send(args) => args(0).radiusify(r, t) //ca ne change pas
      case Sym(arg, _, _, _) => arg.radiusify(r, t) //ca ne change pas
    }
  }

  override def cost(): Cost = {
    this.asInstanceOf[ASTLg] match { //read and Call treated in ASTLt.
      case Coonst(_, _, _) => Cost(0, true, true)

    }
  }

}