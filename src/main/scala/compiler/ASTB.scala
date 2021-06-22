package compiler

import compiler.AST._
import compiler.ASTB._
import compiler.ASTBfun._

import scala.collection._
import scala.language.implicitConversions

sealed class Ring //j'appelle cela Ring parceque ca a une structure d'anneau avec or et and.
class I extends Ring //le type entier n'etends pas boolean, car OR,AND,XOR ne sont pas defini pour les entiers.
final case class B() extends Ring //le type boolean
final case class UI() extends I //unsigned int
final case class SI() extends I //signed int
final case class UISI() extends I
final case class UISIB() extends Ring

/**Identifies AST corresponding to int or bool, excludes those obtained with cons */
trait ASTBt[+R <: Ring] extends AST[R] with MyOpB[R] with MyOpIntB[R] {
  def ring: R = mym.name
  /**sinon y a une erreur du compilo scala empty modifier.*/
  val u = 3;val v = 3
  
}

/**
 * node of Abstract Syntax Tree corresponding to an arithmetic field  boolean, integer (signed or unsigned)
 *  We wish to be able to preserve covariance of R.
 */
sealed abstract class ASTB[+R <: Ring]()(implicit m: repr[R]) extends ASTBt[R]{
 
    
  override def toString: String =  
    this.asInstanceOf[ASTB[_ ]] match { 
      case  Intof (v )=> ""+v 
     case Boolof(v ) => ""+v
 case  Concat2(_,_) => "Concat"
       case Elt(i,_)  => "Elt"+i
 case   Extend (i , _) => "Extend"+i
  case   Xor(_,_) => "Xor" 
  case   Or(_,_) => "Or" 
  case   And(_,_) => "And" 
      case   Neg (_) => "Not"
   case  Mapp1 (_, op )=> "Mapp1"+op.namef
   case  Mapp2 (_,_, op) => "Mapp2"+ op.namef
   case   Scan1 (_, op , _, _, _) => "Scan1"+op.namef
   case   Scan2 (_, _, op , _, _, _) => "Scan2"+op.namef
   case   Reduce (_,  op , _) => "Reduce"+op.namef
    case   Shift (_,right ) =>if(right) ">>" else "<<"
   case  Tminus1 (_) => "tm1" 
    }
}
/** not necessary, just to remember how to retrieve the name*/

/** static object using arithmetic parse trees, operators gets a name, using another method, with the letter 'n' appended  */
object ASTB {

  sealed class Dir
  final case class Left() extends Dir
  final case class Right() extends Dir
  final case class Both() extends Dir

  /**  LSB, Least significant bit has index 0, and is therefore head of list. */
  case class Intof[R <: I](value: Int)(implicit n: repr[R]) extends ASTB[R] with EmptyBag[AST[_]]
  case class Boolof(value: Boolean) extends ASTB[B] with EmptyBag[AST[_]]

  implicit def fromBoolB(d: Boolean): ASTB[B] = Boolof(d)

  //case class ConstSignedInt(val value: Int, val size: Int)(implicit n: repr[SI]) extends ASTB[SI] with EmptyBag[AST[_]] { assert(value < Math.pow(2, size - 1) && value >= -Math.pow(2, size - 1), "not enough bits") }
  //case class ConstUnsignedInt(val value: Int, val size: Int)(implicit n: repr[UI]) extends ASTB[UI] with EmptyBag[AST[_]] { assert(value < Math.pow(2, size) && value >= 0, "not enough bits") }
  /** builds an int from several booleans*/
  //case class Concat[R <: I](exps: Seq[ASTBt[R]])(implicit n: repr[R]) extends ASTB[R] with Neton[AST[_]]
  case class Concat2[R1 <: Ring, R2 <: Ring, O1 <: I](arg: ASTBt[R1], arg2: ASTBt[R2])(implicit n: repr[O1]) extends ASTB[O1] with Doubleton[AST[_]]
  /** returns bit at position i, modulo nbit. So -1 is the index of the last bit.*/
  case class Elt[R <: I](i: Int, arg: ASTBt[R])(implicit n: repr[B]) extends ASTB[B] with Singleton[AST[_]]
  /** will copy the msb*/
  case class Extend[R <: I](i: Int, arg: ASTBt[R])(implicit n: repr[R]) extends ASTB[R] with Singleton[AST[_]]
  //case class Reduce[R<:I](x:ASTB[R],op:redop[ASTB[B]]) extends ASTB[B]
  /**  @param d is a direction. left means from the least significant bits towards the msb, and   right is the other way round.*/
  abstract class ParOp[R <: Ring](d: Dir)(implicit n: repr[R]) extends ASTB[R]
  //case class Or[R <: Ring](val exp: ASTBscal[R], val exp2: ASTBscal[R])(implicit n: repr[R]) extends ParOp[R](Both()) with Doubleton1[AST[_]] //{assert(y.nbit==x.nbit)}
  //case class And[R <: Ring](val exp: ASTBscal[R], val exp2: ASTBscal[R])(implicit n: repr[R]) extends ParOp[R](Both()) with Doubleton1[AST[_]] //{assert(y.nbit==x.nbit)}
  final case class Xor(arg: ASTBt[B], arg2: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Doubleton[AST[_]] //{assert(y.nbit==x.nbit)}
  final case class And(arg: ASTBt[B], arg2: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Doubleton[AST[_]] //{assert(y.nbit==x.nbit)}
  final case class Or(arg: ASTBt[B], arg2: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Doubleton[AST[_]] //{assert(y.nbit==x.nbit)}
  final case class Neg[R <: Ring](arg: ASTBt[R])(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton[AST[_]]
  /** Iterates on one int */
  case class Mapp1[R <: I](arg: ASTBt[R], op: Fundef1[B, B])(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton[AST[_]]
  /** combines aplies an unary boolean op on the bits of an int */
  //case class MappI[R <: I](arg:   ASTBscal[R], op: Fundef1[B,   B])(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton1[AST[_]]
  /** combines a boolean with an int */
  //case class MappBI[R <: I](arg: ASTBscal[B], arg2: ASTBscal[R], op: Fundef2[B, B, B])(implicit n: repr[R]) extends ParOp[R](Both()) with Doubleton1[AST[_]]
  /**  iterates on two ints with identical number of bits*/
  case class Mapp2[R <: I](arg: ASTBt[R], arg2: ASTBt[R], op: Fundef2[B, B, B])(implicit n: repr[R]) extends ParOp[R](Both()) with Doubleton[AST[_]]
  /**  iterate on one int, uses a carry */
  case class Scan1[R <: I](arg: ASTBt[R], op: Fundef2R[B], init: ASTBt[B], d: Dir, initUsed: Boolean)(implicit n: repr[R]) extends ParOp[R](d) with Singleton[AST[_]]
  /**  iterate on two ints with identical  number of bits, uses a carry*/
  case class Scan2[R <: I](arg: ASTBt[R], arg2: ASTBt[R], op: Fundef3R[B], init: ASTBt[B], d: Dir, initUsed: Boolean)(implicit n: repr[R]) extends ParOp[R](d) with Doubleton[AST[_]]
  case class Reduce[R <: I](arg: ASTBt[R], op: Fundef2R[B], init: ASTBt[B])(implicit n: repr[B]) extends ParOp[B](Both()) with Singleton[AST[_]]
  case class Shift[R <: Ring](arg:ASTBt[R],right:Boolean)(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton[AST[_]] 
  case class Tminus1[R <: Ring](arg:ASTBt[R])(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton[AST[_]]
  /*
case class ScanRight1Init[R <: I](exp: ASTBtrait[R], op: Fundef2R[B], init: ASTB1[B])(implicit n: repr[R]) extends ASTB[R]() with Singleton1[AST[_]]
case class ScanLeft1Init[R <: I](exp: ASTB1[R], op: Fundef2R[B], init: ASTB1[B])(implicit n: repr[R]) extends ASTB[R]() with Singleton1[AST[_]]
case class ScanLeft2Init2[R <: I](exp: ASTB1[R], y: ASTB1[R], op: Fundef3R[B], init: ASTB1[B])(implicit n: repr[R]) extends ASTB[R]() with Singleton1[AST[_]] //{assert(y.nbit==x.nbit)}
/**  init, is not part of the result */
case class ScanRight1[R <: I](exp: ASTB1[R], op: Fundef2R[B], init: ASTB1[B])(implicit n: repr[R]) extends ASTB[R]() with Singleton1[AST[_]]
case class ScanRight2[R <: I](exp: ASTB1[R], exp2: ASTB1[R], op: Fundef3R[B], init: ASTB1[B])(implicit n: repr[R]) extends ASTB[R]() with Doubleton1[AST[_]] //{assert(y.nbit==x.nbit)}
*/

  // implicit def toASTB[ R<:I](int i):ASTB[R]=
  
  /*******Wrapping*********/
    def shiftL [R <: Ring](arg:ASTBt[R])(implicit n: repr[R]): Shift[R] =Shift(arg,right = false)
    def shiftR [R <: Ring](arg:ASTBt[R])(implicit n: repr[R]): Shift[R] =Shift(arg,right = true)
  
  
  val lnOf2: Double = scala.math.log(2) // natural log of 2
  val Epsilon = 0.00001 //we add epsilon so that an exact power of two needs one bit more.
  def log2(x: Double): Int = scala.math.ceil(scala.math.log(x) / lnOf2).toInt

  def nbitCte(n: Int, t: I): Int = if (n < 0) { if (t != SI()) throw new RuntimeException("should be signed integer"); 1 + log2(-n - Epsilon) }
  else log2(n + Epsilon) + (if (t == SI()) 1 else 0)
  /**
   * //TODO memoiser pour ne pas avoir a rappeler 40,000 fois add
   *
   * @param nbit stores the number of bits of parameters
   * @param d    the AST we want to know how many bits it has
   * @param pm   memorizes change of parameter 's bit number if any
   * @return bit size of $d
   */
  def nBitR(nbit: immutable.HashMap[AST[_], Int], d: AST[_], pm: mutable.HashMap[Param[_], Int]): Int = {
    /** register parames that needs to be extended, with more bits, because they are combined with Ints having more bits.  */
    def levelup(x: AST[_], a1: Int, a2: Int): Unit = {
      if (a1 < a2) {
        x match { case p: Param[_] => pm += (p -> a2); case _ => throw new RuntimeException("pb bit number in ASTB") }
      }
    } //if not a parameter ca bugge.
    def maxim(x: AST[_], y: AST[_]): Int = {
      val (nx, ny) = (nBitR(nbit, x, pm), nBitR(nbit, y, pm))
      levelup(x, nx, ny); levelup(y, ny, nx); math.max(nx, ny)
    }
    d match {
      case Intof(n)                            => nbitCte(n, d.mym.name.asInstanceOf[I])
      case Boolof(_) => 1
      case Call1(f, e) => nBitR(nbit + (f.p1 -> nBitR(nbit, e, pm)), f.arg, pm)
      case Call2(f, e, e2) => nBitR(nbit + (f.p1 -> nBitR(nbit, e, pm)) + (f.p2 -> nBitR(nbit, e2, pm)), f.arg, pm)
      case e@Param(_) => nbit(e)
      case Neg(x) => nBitR(nbit, x, pm)
      case Xor(_, _) => 1
      case Or(_, _) => 1
      case And(_, _) => 1
      case Scan1(exp, _, _, _, initused) => nBitR(nbit, exp, pm) + (if (initused) 0 else 0)
      case Scan2(exp, exp2, _, _, _, _) => maxim(exp, exp2)
      case Reduce(_, _, _) => 1 //FIXME doesnot work for the reduction with concat
      case Mapp2(exp, exp2, _) => maxim(exp, exp2)

      case Mapp1(exp, _) => nBitR(nbit, exp, pm)
      //case MappBI(exp, exp2, opp)               => nBitR(nbit, exp2, pm)
      case Elt(_, _) => 1;
      case Concat2(exp, exp2) => nBitR(nbit, exp2, pm) + nBitR(nbit, exp, pm) //
      case Extend(n, _) => n
    }
  }
  /* class NamedFunction2[T1, T2, R](name: String, f: Function2[T1, T2, R]) extends Function2[T1, T2, R] {
    def apply(a: T1, b: T2): R = f.apply(a, b); override def toString = name
  }
  class NamedFunction1[T1, R](name: String, f: Function1[T1, R]) extends Function1[T1, R] {
    def apply(a: T1): R = f.apply(a); override def toString = name
  }*/
  // type op2B[R <: Ring] = NamedFunction2[ASTB[B], ASTB[R], ASTB[R]];
  // type op2[R <: Ring] = NamedFunction2[ASTB[R], ASTB[R], ASTB[R]];
  // type op1[R1 <: Ring, R2 <: Ring] = NamedFunction1[ASTB[R1], ASTB[R2]];
  // type opN[R1 <: Ring, R2 <: Ring] = NamedFunction1[Seq[ASTB[R1]], ASTB[R2]];
  // val concatN: Fundefn[I, I   ] = {}
  //def concatN[R <: I](implicit n: repr[R]) = new opN[R, R]("concat", Concat[R](_))

}

 

