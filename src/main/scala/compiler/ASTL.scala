package compiler

import com.sun.xml.internal.bind.v2.runtime.reflect.opt.Const
import compiler.AST._
import compiler.ASTB._
import compiler.ASTBfun._
import compiler.ASTL._
import dataStruc.Align._
import compiler.Constraint._
import compiler.Circuit.{iTabSymb2, _}
import compiler.repr._

import scala.collection.{mutable, _}
import scala.reflect.ClassTag


/**
 * At some point, we decided to store the type information for each distinct constructor, in order to have direct access to this info when copying the constructor,
 * this enabled to enforce the covariance in L:Locus and R:Ring, which was intuitive and would therefore facilitate things later on.
 * but then we abandonned it, so we could come back to previous setting where type was not stored, and copied in case class copying (see ASTBs).
 */
object ASTL {
  val u = 1

  private[ASTL] case class Coonst[L <: Locus, R <: Ring](cte: ASTB[R], m: repr[L], n: repr[R]) extends ASTL[L, R]()(repr.nomLR(m, n)) with EmptyBag[AST[_]]

  private[ASTL] final case class Broadcast[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[S1, R], m: repr[T[S1, S2]], n: repr[R])
    extends ASTL[T[S1, S2], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]

  private[ASTL] final case class Send[S1 <: S, S2 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, S2]], n: repr[R])
    extends ASTL[T[S1, S2], R]() with Neton[AST[_]]

  private[ASTL] final case class Transfer[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R], m: repr[T[S2, S1]], n: repr[R])
    extends ASTL[T[S2, S1], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]

  private[ASTL] final case class Unop[L <: Locus, R1 <: Ring, R2 <: Ring](op: Fundef1[R1, R2], arg: ASTLt[L, R1], m: repr[L], n: repr[R2])
    extends ASTL[L, R2]()(repr.nomLR(m, n)) with Singleton[AST[_]]

  private[ASTL] final case class Binop[L <: Locus, R1 <: Ring, R2 <: Ring, R3 <: Ring](op: Fundef2[R1, R2, R3], arg: ASTLt[L, R1], arg2: ASTLt[L, R2], m: repr[L], n: repr[R3])
    extends ASTL[L, R3]()(repr.nomLR(m, n)) with Doubleton[AST[_]]

  private[ASTL] final case class Redop[S1 <: S, S2 <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R], m: repr[S1], n: repr[R])
    extends ASTL[S1, R]()(repr.nomLR(m, n)) with Singleton[AST[_]] {
    /** used to compute the expression being reduced.  */
    override def redExpr: List[AST[_]] = List(arg)
  }

  private[ASTL] final case class Clock[S1 <: S, S2 <: S, S3 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R], dir: Boolean)(implicit m: repr[T[S1, S3]], n: repr[R])
    extends ASTL[T[S1, S3], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]

  private[ASTL] final case class Sym[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R], m: repr[T[S1, S2new]], t: CentralSym[S2, S1, S2new], n: repr[R])
    extends ASTL[T[S1, S2new], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]

  /** Field which has a value both  at time t, and t+1 */
  trait Strate[L <: Locus, R <: Ring] {
    val pred: ASTLt[L, R];
    val next: ASTLt[L, R]
  }

  /** Unlike other constructors,  Layer is not defined as a case class, otherwise equality between two layer of identical number of bits would allways hold */
  abstract class Layer[L <: Locus, R <: Ring](val nbit: Int)(implicit m: repr[L], n: repr[R]) extends ASTL[L, R]() with EmptyBag[AST[_]] with Strate[L, R] {
    val v = 1
    /** the value at t, which  is represented as  the layer itself. */
    val pred: ASTL[L, R] = this

    /** @param a allows to visualize "this" with a minimalistic coloring load on the screen */
    def render(a: ASTL.ASTLg) {
      sysInstr ::= UsrInstr.display(a).asInstanceOf[UsrInstr[AST[_]]]
    }

    /** needed to visite the next fields */
    override def other: List[AST[_]] = next :: super.other

    /** instructions also includes updating the layer by storing the next value.  */
    override def sysInstrs: List[UsrInstr[AST[_]]] = UsrInstr.memorize(next).asInstanceOf[UsrInstr[AST[_]]] :: super.sysInstrs
  }


  def rotL[T](a: Array[T])(implicit m: ClassTag[T]): Array[T] = a.drop(1) :+ a(0)

  def rotR[T](a: Array[T])(implicit m: ClassTag[T]): Array[T] = a(a.length - 1) +: a.take(a.length - 1)

  def rotR[T](a: Array[T], jump: Int)(implicit m: ClassTag[T]): Array[T] = Array.concat(a.drop(jump), a.take(jump))

  def rot[T](a: Array[T], dir: Boolean)(implicit m: ClassTag[T]): Array[T] = if (dir) rotR(a) else rotL(a) //dir=True correspond to trigonometric order
  def rotPerm(dec: Int): Array[Int] = {
    val r = new Array[Int](6); for (i <- 0 to 5) r(i) = (i + dec) % 6; r
  }

  def composeAll(p: Array[Int], t: iTabSymb[Array[Int]]): Map[String, Array[Int]] = t.map { case (k, v) => k -> compose(p, v) }

  def composeAll2(p: Array[Int], t: iTabSymb2[Array[Int]]): iTabSymb2[Array[Int]] = t.map { case (k, v) => k -> compose(p, v) }

  import scala.language.implicitConversions

  /** Allows to consider false and true as occurence of ASTLs */
  implicit def fromBool[L <: Locus](d: Boolean)(implicit m: repr[L]): ASTLt[L, B] = Coonst(Boolof(d), m, repr.nomB)

  /** Allows to consider integers as occurence of ASTLs */
  implicit def fromInt[L <: Locus, R <: I](d: Int)(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = Coonst(Intof(d)(n), m, n)

  type ASTLg = ASTLt[_ <: Locus, _ <: Ring]
  type rewriteASTLt[L <: Locus, R <: Ring] = ASTLt[L, R] => ASTLt[L, R]
  //type bij2[L <: Locus, R <: Ring] = ASTL[L, R] => ASTL[L, R]

  /** ***************the wrapper *******************/
  def displayIn(l: Layer[_ <: Locus, _ <: Ring], f: ASTLg): Unit = l.render(f)

  def bugIfIn(l: Layer[_ <: Locus, _ <: Ring], f: ASTL[_ <: Locus, B]): Unit = l.bugif(f)

  def const[L <: Locus, R <: Ring](cte: ASTB[R])(implicit m: repr[L], n: repr[R]): Coonst[L, R] = Coonst(cte, m, n)

  def sym[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], t: CentralSym[S2, S1, S2new], n: repr[R]): Sym[S1, S2, S2new, R] = Sym(arg, m, t, n)

  def v[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, V]], n: repr[R]): Broadcast[S1, V, R] = Broadcast[S1, V, R](arg, m, n); // for broadcast, we want to specify only the direction where broadcasting takes place.
  def e[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, E]], m2: repr[T[E, S1]], n: repr[R]): Broadcast[S1, E, R] = Broadcast[S1, E, R](arg, m, n); // this is done using three function e,v,f.
  def f[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, F]], m2: repr[T[F, S1]], n: repr[R]): Broadcast[S1, F, R] = Broadcast[S1, F, R](arg, m, n)


  def clock[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Clock[S1, S2, S2new, R] = Clock[S1, S2, S2new, R](arg, dir = true)

  def anticlock[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Clock[S1, S2, S2new, R] = Clock[S1, S2, S2new, R](arg, dir = false)


  //Build a transfer, just like v,e,f, however specify a diffent Simplicial field for each component.
  def sendv[S1 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, V]], n: repr[R]): Send[S1, V, R] = {
    assert(args.length == 6 / args.head.locus.density); Send[S1, V, R](args);
  } //TODO check the length of args
  // def sende[S1 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, E]], n: repr[R]) = Send[S1, E, R](args) ;
  //  def sendf[S1 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, F]], n: repr[R]) = Send[S1, F, R](args) ;

  //def castB2R[L<:Locus,R<:I]( arg: AST[L,B] )(implicit m : repr[L])  = Unop[L,B,R] (castB2RN[R],arg );
  def transfer[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S2, S1]], n: repr[R]): Transfer[S1, S2, R] = Transfer(arg, m, n)

  //def unop[L <: Locus, Ri <: Ring, Ro <: Ring](f: Fundef1[Ri, Ro])(implicit m: repr[L], n: repr[Ro]) = (arg1: ASTLt[L, Ri]) => Unop[L, Ri, Ro](f, arg1, m, n)
  def sign[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): ASTLt[L, SI] = Unop[L, SI, SI](ASTBfun.sign, arg1, m, nomSI)

  def halve[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = Unop[L, R, R](halveB.asInstanceOf[Fundef1[R, R]], arg1, m, n)

  def orScanRight[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, R, R] = Unop[L, R, R](halveB.asInstanceOf[Fundef1[R, R]], arg1, m, n)

  def gt[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): Unop[L, SI, B] = Unop[L, SI, B](elt(-1).asInstanceOf[Fundef1[SI, B]], arg1, m, repr.nomB); //-1 will be taken modulo nbit.
  def notNull[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, R, B] = Unop[L, R, B](notNullB.asInstanceOf[Fundef1[R, B]], arg1, m, repr.nomB)

  /** Instead of casting boolean to integer,  we define a logical and taking an int and a  bool */
  def andLB2R[L <: Locus, R <: I](arg1: ASTLt[L, B], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Binop[L, B, R, R] = Binop[L, B, R, R](andLBtoR.asInstanceOf[Fundef2[B, R, R]], arg1, arg2, m, n)

  def elem[L <: Locus, R <: I](i: Int, arg: ASTLt[L, R])(implicit m: repr[L], n: repr[B]): Unop[L, R, B] = Unop[L, R, B](elt(i).asInstanceOf[Fundef1[R, B]], arg, m, n)

  def concat2[L <: Locus, R1 <: Ring, R2 <: Ring](arg1: ASTLt[L, R1], arg2: ASTLt[L, R2])(implicit m: repr[L], n: repr[I]): ASTL[L, I] = Binop(concat2f.asInstanceOf[Fundef2[R1, R2, I]], arg1, arg2, m, n)

  def extend[L <: Locus, R <: Ring](i: Int, arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, R, R] = Unop[L, R, R](ASTBfun.extend(i).asInstanceOf[Fundef1[R, R]], arg, m, n)

  //def concat[L <: Locus, R <: I](arg1: Seq[ASTLtrait[L, R]])(implicit m: repr[L], n: repr[R]) = Multop2[L, R, R](concatN, arg1,m,n);
  // def orR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]) = Redop[S1, S2, R]((orI.asInstanceOf[Fundef2[R, R, R]], False[R]), arg, m, n);
  def orR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] = Redop[S1, S2, R](orRedop[R], arg, m, n)

  def andR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] = Redop[S1, S2, R](andRedop[R], arg, m, n)

  def xorR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] = Redop[S1, S2, R](xorRedop[R], arg, m, n)

  def redOp2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Binop[T[S1, S2new], R, R, R] =
    Binop[T[S1, S2new], R, R, R](op._1, Clock[S1, S2, S2new, R](arg, dir = true), Clock[S1, S2, S2new, R](arg, dir = false), m, n)

  def xorR2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Binop[T[S1, S2new], R, R, R] =
    redOp2[S1, S2, S2new, R](xorRedop[R], arg)

  def subESI[S2 <: S](arg: ASTLt[T[E, S2], SI])(implicit m: repr[E]): ASTLt[E, SI] =
    Redop[E, S2, SI]((subSI, Intof[SI](0)), arg, m, repr.nomSI).asInstanceOf[ASTLt[E, SI]]

  /** minR has two implementations depending if the integers to be compared are signed or unsigned. */
  def minR[S1 <: S, S2 <: S, R <: I](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): ASTLt[S1, R] =
    if (arg.ring == SI()) Redop[S1, S2, SI]((minSI, Intof[SI](0)), arg.asInstanceOf[ASTLt[T[S1, S2], SI]], m, repr.nomSI).asInstanceOf[ASTLt[S1, R]]
    else Redop[S1, S2, UI]((minUI, Intof[UI](0)), arg.asInstanceOf[ASTLt[T[S1, S2], UI]], m, repr.nomUI).asInstanceOf[ASTLt[S1, R]]

  /** Delayed uses a trick found on the net, to have a call by name, together with a case class necessary to make the match */
  def delayedL[L <: Locus, R <: Ring](_arg: => ASTLt[L, R])(implicit m: repr[(L, R)]): ASTLt[L, R] = {
    lazy val delayed = _arg; new Delayed[(L, R)](() => delayed) with ASTLt[L, R]
  }

  def cond[L <: Locus, R <: I](b: ASTLt[L, B], arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] =
    andLB2R[L, R](b, arg1) | andLB2R(~b, arg2)

  /**
   * computes an int with a single non zero bit which is the highest rank for which operand's bit is one if operand is null, output O.
   * this is an example of boolean function with a reused value: orScanRight.
   */
  def mstb[L <: Locus, R <: I](arg1: ASTL[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = {
    val y: ASTL[L, R] = orScanRight[L, R](arg1); y ^ halve(y)
  }

  def or[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg1.ring match {
    case B() => Binop(orB, arg1.asInstanceOf[ASTLt[L, B]], arg2.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case _ => Binop(orI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2, m, n)
  }).asInstanceOf[ASTL[L, R]]

  def and[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg1.ring match {
    case B() => Binop(andB, arg1.asInstanceOf[ASTLt[L, B]], arg2.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case _ => Binop(andI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2, m, n)
  }).asInstanceOf[ASTL[L, R]]

  def xor[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg1.ring match {
    case B() => Binop(xorB, arg1.asInstanceOf[ASTLt[L, B]], arg2.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case _ => Binop(xorI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2, m, n)
  }).asInstanceOf[ASTL[L, R]]

  def neg[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg.ring match {
    case B() => Unop(negB, arg.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case _ => Unop(negI.asInstanceOf[Fundef1[R, R]], arg, m, n)
  }).asInstanceOf[ASTL[L, R]]

  def opp[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, SI, SI] = Unop[L, SI, SI](oppSI, arg.asInstanceOf[ASTLt[L, SI]], m, repr.nomSI)

  //{ ASTL.Unop(opp.asInstanceOf[Fundef1[R, SI]], this, m, repr.nomSI) }


  /** uses a fixed val addUISI, and let the compiler believe that this val has the appropriate expected  type R=UI or R=SI  */
  def add[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = Binop(addUISI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2, m, n)

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
  override def toString: String =
    this.asInstanceOf[ASTL[_, _]] match {
      //  case Layer(s, _)                 => "Layer " + this.name + ":" + locus.toString.charAt(0) + "-" + ring.toString.charAt(0)
      case _: Layer[_, _] => "Layer " + this.name + ":" + locus.toString.charAt(0) + "-" + ring.toString.charAt(0)
      case Binop(op, _, _, _, _) => op.namef
      case Coonst(cte, _, _) => "Const" + cte.toString + locus.toString.charAt(0) + "_" + ring.toString.substring(0, ring.toString.length() - 2);

      //  case Multop(op, args,_,_)      => op.toString
      case Unop(op, _, _, _) => op.namef
      case Redop(op, _, _, _) => "red" + op._1.namef
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
   *         No  override, because signagure is distinct from AST's propagate */
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
      case e@Clock(a, _) => e.copy(arg = id2(a))(lpart(e.mym), rpart(e.mym))
      case e@Sym(a, _, _, _) => e.copy(arg = id2(a))
    };
    newD.setName(this.name);
    newD.asInstanceOf[ASTL[L, R]]
  }

  //
  //  override def nbit(cur: ProgData1[_], nbitLB: AstField[Int], tSymb: TabSymb[InfoNbit[_]], newFuns: TabSymb[ProgData2]): ASTLt[L, R] = {
  //    val nbitB = immutable.HashMap.empty[AST[_], Int] //stores the bit number of an ASTB expression
  //    val nbitP = mutable.HashMap.empty[Param[_], Int] //virgin, to retrieve the nbits computed for the param.
  //    val result = this match {
  //      case Binop(op, a, a2, l2, r2) => //BINOP needs more work, because it triggers possible insertion of a new node "extend";
  //        var anew = a.nbit(cur, nbitLB, tSymb, newFuns); var a2new = a2.nbit(cur, nbitLB, tSymb, newFuns)
  //        //we start evaluation of binop by adding the number of bits of the arguments
  //        val startnbitB = nbitB + (op.p1 -> nbitLB(anew)) + (op.p2 -> nbitLB(a2new))
  //        val nbitResult = ASTB.nBitR(startnbitB, op.arg, nbitP) //retrieves the number of bit computed from the call to the ASTBfun.
  //        if (nbitP.contains(op.p1)) anew = anew.extendMe(nbitP(op.p1))
  //        if (nbitP.contains(op.p2)) a2new = a2new.extendMe(nbitP(op.p2))
  //        val newthis = Binop(op, anew, a2new, l2, r2)
  //        nbitLB += newthis -> nbitResult //the hashtable stores the number of bits of the newly computed tree.
  //        newthis
  //      case _ => //in all the other cases, no change is done on the AST, only  nbitLB is updated.
  //        val newthis = this.propagateASTL((d: ASTLt[L, R]) => d.nbit(cur, nbitLB, tSymb, newFuns))
  //
  //        def newNbit() = nbitLB(newthis.asInstanceOf[Singleton[AST[_]]].arg) //the nbit value of the arg is stored in nbitLB
  //        nbitLB += newthis -> (newthis.asInstanceOf[ASTL[_, _]] match {
  //          // case l:Layer[_,_] =>  l.nbit
  //          case Coonst(cte, _, _) => ASTB.nBitR(nbitB, cte, nbitP)
  //          case Unop(op, _, _, _) => ASTB.nBitR(nbitB + (op.p1 -> newNbit()), op.arg, nbitP)
  //          case Redop(_, _, _, _) | Clock(_, _) | Transfer(_, _, _) | Broadcast(_, _, _) | Sym(_, _, _, _) => newNbit()
  //          case Send(_) => nbitLB(newthis.asInstanceOf[Neton[AST[_]]].args.head)
  //          //FIXME for the concat redop, the number of bit must take into account the arity (2,3, or 6)
  //        })
  //        newthis
  //    };
  //    result.setName(this.name);
  //    result
  //  }
  //
  /**
   * * @param cur The current programm
   * * @param nbitLB Stores number of bits of subfields.
   * * @param tSymb The symbol table with number of bits
   * * @param newFuns Functions generated
   * * @return Expression rewritten so as to include Extend, when binop operators are used,
   * and one of the two operands has not enough bits.
   *
   */
  override def bitIfy(cur: DataProg[_, InfoType[_]], nbitLB: AstField[Int], tSymb: TabSymb[InfoNbit[_]],
                      newFuns: TabSymb[DataProg[_, InfoNbit[_]]]): ASTLt[L, R] = {
    val nbitB = immutable.HashMap.empty[AST[_], Int] //stores the bit number of an ASTB expression
    val nbitP = mutable.HashMap.empty[Param[_], Int] //virgin, to retrieve the nbits computed for the param.
    val result = this match {
      case Binop(op, a, a2, l2, r2) => //BINOP needs more work, because it triggers possible insertion of a new node "extend";
        var anew = a.bitIfy(cur, nbitLB, tSymb, newFuns);
        var a2new = a2.bitIfy(cur, nbitLB, tSymb, newFuns)
        //we start evaluation of binop by adding the number of bits of the arguments
        val startnbitB = nbitB + (op.p1 -> nbitLB(anew)) + (op.p2 -> nbitLB(a2new))
        val nbitResult = ASTB.nBitR(startnbitB, op.arg, nbitP) //retrieves the number of bit computed from the call to the ASTBfun.
        if (nbitP.contains(op.p1)) anew = anew.extendMe(nbitP(op.p1))
        if (nbitP.contains(op.p2)) a2new = a2new.extendMe(nbitP(op.p2))
        val newthis = Binop(op, anew, a2new, l2, r2)
        nbitLB += newthis -> nbitResult //the hashtable stores the number of bits of the newly computed tree.
        newthis
      case _ => //in all the other cases, no change is done on the AST, only  nbitLB is updated.
        val newthis = this.propagateASTL((d: ASTLt[L, R]) => d.bitIfy(cur, nbitLB, tSymb, newFuns))

        def newNbit() = nbitLB(newthis.asInstanceOf[Singleton[AST[_]]].arg) //the nbit value of the arg is stored in nbitLB
        nbitLB += newthis -> (newthis.asInstanceOf[ASTL[_, _]] match {
          // case l:Layer[_,_] =>  l.nbit
          case Coonst(cte, _, _) => ASTB.nBitR(nbitB, cte, nbitP)
          case Unop(op, _, _, _) => ASTB.nBitR(nbitB + (op.p1 -> newNbit()), op.arg, nbitP)
          case Redop(_, _, _, _) | Clock(_, _) | Transfer(_, _, _) | Broadcast(_, _, _) | Sym(_, _, _, _) => newNbit()
          case Send(_) => nbitLB(newthis.asInstanceOf[Neton[AST[_]]].args.head)
          //FIXME for the concat redop, the number of bit must take into account the arity (2,3, or 6)
        })
        newthis
    };
    result.setName(this.name);
    result
  }

  /**
   * @return true if the expression is only a concatenation of elements   */
  override def justConcats: Boolean = this match {
    case Unop(Fundef1("elt", _, _), arg, _, _) => arg.justConcats
    case Binop(Fundef2("concat", _, _, _), arg, arg2, _, _) => arg.justConcats && arg2.justConcats
    case _ => super.justConcats
  }

  override def unfoldSimplic(m: Machine): ArrAst = {
    val r = rpart(mym.asInstanceOf[repr[(L, R)]])
    val s = this.locus.asInstanceOf[S]
    this.asInstanceOf[ASTLg] match {
      case Coonst(cte, _, _) => Array.fill(s.sufx.length)(cte)
      case Broadcast(_, _, _) => throw new RuntimeException("Broadcast creates   a transfer type")
      case Send(_) => throw new RuntimeException("Broadcast creates   a transfer type")
      case Transfer(_, _, _) => throw new RuntimeException("Transfer creates   a transfer type")
      case Unop(op, a, _, _)  => a.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m).map(new Call1(op.asInstanceOf[Fundef1[Any, R]], _)(r) with ASTBt[R])
      case Binop(op, a, a2, _, _) => a.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m).zip(a2.unfoldSimplic(m)).map({
        case (c, c2) => new Call2(op.asInstanceOf[Fundef2[Any, Any, R]], c, c2)(r) with ASTBt[R].asInstanceOf[ASTBg]
      })
      case Redop(op, a, _, _) =>
        def reduce(as: Array[ASTBt[R]], opred: redop[R]) = as.toList.tail.foldLeft(as(0))(new Call2(opred._1, _, _)(r) with ASTBt[R])
        a.unfoldTransfer(m).map((x: ArrAst) => reduce(x.asInstanceOf[Array[ASTBt[R]]], op.asInstanceOf[redop[R]])).asInstanceOf[ArrAst]
      case Clock(_, _) => throw new RuntimeException("Clock creates    a transfer type")

      case Sym(_, _, _, _)     => throw new RuntimeException("Sym creates  a transfer type")
    }
    //read and Call treated in ASTLt.

  }
  override def unfoldTransfer(m: Machine): ArrArrAst = {
    val T(s1, des) = this.locus; val l2 = this.locus.sufx.length
    this.asInstanceOf[ASTLg] match {
      case Coonst(cte, _, _) => Array.fill(s1.sufx.length, l2)(cte)
      case Broadcast(a, _, _) => a.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m).map(Array.fill(l2)(_))
      case Send(a) =>
        if (a.length != l2) throw new RuntimeException("incorrect number of arguments for send")
        a.toArray.map(_.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m)).transpose
      case Transfer(a, _, _) => m(des, s1, a.unfoldTransfer(m))
      case Unop(op, a, _, n) => a.unfoldTransfer(m).map(_.map(new Call1(op.asInstanceOf[Fundef1[Any, R]], _)(n.asInstanceOf[repr[R]]) with ASTBt[R].asInstanceOf[ASTBg]))
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
        val T(s1, src) = a.locus; val atr = a.unfoldTransfer(m).map(rotR(_)); s1 match {
          case V() => atr.map(rotR(_)).map(rotR(_))//throw new RuntimeException("sym not defined on V in the general case")
          case E() => atr // la composée de deux rotation est une rotation simple qui est aussi une permutation pour E.
          case F() => if (src < des) atr else atr.map(rotR(_)) //we follow trigonometric, the composition of tree anticlock  must add one rotation, if not(src<des).
      }
      //read and Call treated in ASTLt.
    }
  }

  def shouldAffect: Boolean = this match {
    case Redop(_, _, _, _) => true
    case Binop(_, a1, a2, _, _) => a1.isInstanceOf[ASTL.Clock[_, _, _, _]] || a2.isInstanceOf[ASTL.Clock[_, _, _, _]] || a1.isInstanceOf[ASTL.Sym[_, _, _, _]] || a2.isInstanceOf[ASTL.Sym[_, _, _, _]] //that's an overkill, unnecessary introduced variables will have to be removed
    case _ => false
  }

  /**
   *
   * @return tree with some id being replaced by shifted version,
   *         cycle constraint, instruction setting the shifted version, alignement with respect to used variables.
   */
  override def align3(r: Result): ASTLt[L, R] = {
    val newExp = this.asInstanceOf[ASTLg] match { //read and Call treated in ASTLt.
      case Coonst(_, _, _) => this
      case Broadcast(arg, _, _) => r.algn = r.algn.map { case (k, v) => k -> arg.locus.proj }; this //does not depend on v, because v is constant
      case e@Send(args) => val newArgs = args.map(_.align3(r)) //collects results in $r
        r.algn = r.algn.map { case (k, v) => k -> args.head.locus.proj } //does not depend on v, because v is constant
        e.copy(args = newArgs)(lpart(e.mym), rpart(e.mym))
      case e@Transfer(arg, _, _) =>
        val T(s1, s2) = arg.locus;
        val t = hexPermut((s1, s2));
        val newArg = arg.align3(r);
        r.c = permute(r.c, t, e.locus);
        r.algn = composeAll2(t, r.algn)
        e.copy(arg = newArg)
      case e@Unop(_, arg, _, _) => e.copy(arg = arg.align3(r))
      case e@Binop(_, arg, arg2, _, _) =>
        var newArg = arg.align3(r)
        val algn = r.algn
        val newArg2 = arg2.align3(r)
        val k = algn.keys.toSet.intersect(r.algn.keys.toSet);
        assert(k.size <= 1, " more than one to aligne !")
        if (k.nonEmpty && !(algn(k.head) sameElements r.algn(k.head))) { //k is the aux defined by an instr which will have to use two registers.
          val e = k.head //here we assume that there is a single input variable
          val perm = compose(invert(algn(e)), r.algn(e))
          val shiftedE = "shift" + e
          r.c = intersect(r.c, Some(Cycle(perm, locus.asInstanceOf[TT])))
          val shiftInstr = ShiftInstr(shiftedE, e, perm)
          r.si += e -> shiftInstr //TODO le alignperm de shiftInstr on peut le faire ensuite!
          r.algn += shiftedE -> algn(e)
          newArg = newArg.replaceBy(e, shiftedE)
        }
        e.copy(arg = newArg, arg2 = newArg2)
      case e@Redop(_, arg, _, _) => e.copy(arg = arg.align3(r))
      case e@Clock(arg, dir) =>
        val newArg = arg.align3(r)
        val T(_, des) = this.locus;
        val T(_, src) = arg.locus;
        val trigo = !dir;
        val atr = rotPerm(if (trigo) 1 else 5) //faudrait vérifier is c'est pas le contraire
        if ((src < des) ^ dir) {
          r.c = permute(r.c, atr, e.locus); r.algn = composeAll2(atr, r.algn)
        }
        e.copy(arg = newArg)(lpart(e.mym), rpart(e.mym))
      case e@Sym(arg, _, _, _) => val newArg = arg.align3(r)
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
   * @return tree with some id being replaced by shifted version,
   *         cycle constraint, instruction setting the shifted version, alignement with respect to used variables.
   */
  override def align2: (ASTLg, Option[Constraint], iTabSymb2[ShiftInstr], iTabSymb2[Array[Int]]) =
    this.asInstanceOf[ASTLg] match { //read and Call treated in ASTLt.
      case Coonst(_, _, _) => (this, None, immutable.HashMap.empty, immutable.HashMap.empty)
      case Broadcast(arg, _, _) =>
        val toto = arg.align2;
        val tree = toto._1;
        val algn = toto._4
        (tree.asInstanceOf[ASTLg], None, immutable.HashMap.empty, algn.map { case (k, _) => k -> arg.locus.proj }) //does not depend on v, because v is constant
      case e@Send(args) => {
        var newArgs = List[ASTLt[S, Ring]]()
        var aligns: iTabSymb2[Array[Int]] = immutable.HashMap.empty[String, Array[Int]]
        for (arg <- args) {
          val toto = arg.align2
          val tree = toto._1
          val algn = toto._4
          newArgs = tree.asInstanceOf[ASTLt[S, Ring]] :: newArgs
          aligns ++= algn.map({ case (k, _) => k -> arg.locus.proj }) //Todo we could have the same pb has in binop here.
        }
        (e.copy(args = newArgs)(lpart(e.mym), rpart(e.mym)), None, immutable.HashMap.empty, aligns)
      }
      case e@Transfer(arg, _, _) =>
        val T(s1, s2) = arg.locus;
        val t = hexPermut((s1, s2));
        val toto = arg.align2
        val tree = toto._1
        val algn = toto._4
        val c = toto._2
        val instrs = toto._3
        (e.copy(arg = tree.asInstanceOf[ASTLt[T[S, S], Ring]]), permute(c, t, e.locus), instrs, composeAll2(t, algn))
      case e@Unop(_, arg, _, _) => val toto = arg.align2
        val tree = toto._1
        val algn = toto._4
        val c = toto._2
        val instrs = toto._3
        (e.copy(arg = tree.asInstanceOf[ASTLt[Locus, Ring]]), c, instrs, algn)

      case e@Binop(_, arg, arg2, _, _) =>
        //We compute the cycle  constraint here, because we can
        val toto = arg.align2
        val tree = toto._1
        val algn = toto._4
        val c = toto._2
        val instrs = toto._3
        var newTree = tree
        val toto2 = arg2.align2
        val tree2 = toto2._1
        val algn2 = toto2._4
        val c2 = toto2._2
        val instrs2 = toto2._3
        var c3 = intersect(c, c2)
        var newInstr = instrs ++ instrs2
        var newAlign = algn ++ algn2 //arg2 has priority over arg if re-use
        val k = algn.keys.toSet.intersect(algn2.keys.toSet)
        if (k.nonEmpty) { //k is the aux defined by an instr which will have to use two registers.
          val e = k.head //here we assume that there is a single input variable
          assert(k.size == 1, " more than one to aligne !")
          if (!(algn(e) sameElements algn2(e))) {
            val perm = compose(invert(algn(e)), algn2(e))
            val shiftedE = "shift" + e
            c3 = intersect(c3, Some(Cycle(perm, locus.asInstanceOf[TT])))
            val shiftInstr = ShiftInstr(shiftedE, e, perm)
            newInstr += e -> shiftInstr //TODO le align perm on peut le faire ensuite!
            newAlign += shiftedE -> algn(e)
            newTree = tree.replaceBy(e, shiftedE)
          }
        }
        (e.copy(arg = newTree.asInstanceOf[ASTLt[Locus, Ring]], arg2 = tree2.asInstanceOf[ASTLt[Locus, Ring]]), c3, newInstr, newAlign)

      case Redop(_, arg, _, _) => //we compute a constraint, that is implicitely, the constraint to be checked for partitionning the Reduction.
        val (_, c, instrs, algn) = arg.align2
        (this, c, instrs, algn) //Redop is done in 6 instruction that will be scheduled according to the alignemet of its operand.
      //note that here, the expression has a simplicial type, thus, the alignement is not used to compute an alignement to a root,
      //it will be used to schedule the 6 redop operations. we will have to compose with the alignement to the root of the reduced transfer variable.
      case e@Clock(arg, dir) =>
        val toto = arg.align2
        val tree = toto._1
        val algn = toto._4
        val c = toto._2
        val instrs = toto._3
        val T(_, des) = this.locus;
        val T(_, src) = arg.locus;
        val trigo = !dir;
        val atr = rotPerm(if (trigo) 1 else 5) //faudrait vérifier is c'est pas le contraire
        val newTree = e.copy(arg = tree.asInstanceOf[ASTLt[T[S, S], Ring]])(lpart(e.mym), rpart(e.mym))
        if ((src < des) ^ dir) (newTree, c, instrs, algn)
        else (newTree, permute(c, atr, arg.locus), instrs, composeAll2(atr, algn))
      case e@Sym(arg, _, _, _) =>
        val toto = arg.align2
        val tree = toto._1
        val algn = toto._4
        val c = toto._2
        val instrs = toto._3
        val newTree = e.copy(arg = tree.asInstanceOf[ASTLt[T[S, S], Ring]])
        val T(_, des) = this.locus;
        val T(s1, src) = arg.locus;
        val atr = rotPerm(s1 match { case E() => 1 case F() => if (src < des) 1 else 2 case V() => 3 })
        (newTree, permute(c, atr, arg.locus), instrs, composeAll2(atr, algn))
      /* case l: Layer2[_, _] => immutable.HashMap(l.name -> l.locus.neutral)
       */

    }

  /**
   *
   * @param cs
   * @param v
   * @return
   */
  override def align(cs: TabConstr, v: String): iTabSymb[Array[Int]] = {
    this.asInstanceOf[ASTLg] match { //read and Call treated in ASTLt.
      case Coonst(_, _, _) => immutable.HashMap()
      case Broadcast(arg, _, _) => arg.align(cs, v).map { case (k, _) => k -> arg.locus.proj } //does not depend on v, because v is constant
      case Send(args) => immutable.HashMap.empty ++ args.flatMap(a => a.align(cs, v).map { case (k, _) => k -> a.locus.proj }) //we can make  a union because does not depend on v
      case Transfer(arg, _, _) =>
        val T(s1, s2) = arg.locus; val t = hexPermut((s1, s2)); composeAll(t, arg.align(cs, v))
      case Unop(_, arg, _, _) => arg.align(cs, v)
      case Binop(_, arg, arg2, _, _) =>
        //be compute the constraint cycle here, because we can
        val a1 = arg.align(cs, v);
        val a2 = arg2.align(cs, v)
        val k = a1.keys.toSet.intersect(a2.keys.toSet)
        if (k.nonEmpty) { //k is the aux defined by an instr which will have to use two registers.
          val e = k.head //here we assume that there is a single input variable
          if (!(a1(e) sameElements a2(e)))
            cs += v -> Cycle(compose(invert(a1(e)), a2(e)), locus.asInstanceOf[TT]);

        }
        a1 ++ a2 //arg2 has priority over arg if non equal
      case Redop(_, arg, _, _) => //we compute a constraint, that is implicitely, the constraint to be checked for partitionning the Reduction.

        arg.align(cs, v) //Redop is done in 6 instruction that will be scheduled according to the alignemet of its operand.
      //note that here, the expression has a simplicial type, thus, the alignement is not used to compute an alignement to a root,
      //it will be used to schedule the 6 redop operations. we will have to compose with the alignement to the root of the reduced transfer variable.


      case Clock(arg, dir) =>
        val T(_, des) = this.locus;
        val T(_, src) = arg.locus;
        val trigo = !dir;
        val atr = rotPerm(if (trigo) 1 else 5) //faudrait vérifier is c'est pas le contraire
        if ((src < des) ^ dir) arg.align(cs, v) else composeAll(atr, arg.align(cs, v))
      case Sym(arg, _, _, _) =>
        val T(_, des) = this.locus; val T(s1, src) = arg.locus; val atr = rotPerm(s1 match { case E() => 1 case F() => if (src < des) 1 else 2 case V() => 3 }); composeAll(atr, arg.align(cs, v))
      case l: Layer[_, _] => immutable.HashMap(l.name -> l.locus.neutral)
    }
  }
}

