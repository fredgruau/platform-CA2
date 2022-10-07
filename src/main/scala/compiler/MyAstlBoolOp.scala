package compiler

import ASTL._
import compiler.ASTB.{False, Intof, True}
/**
 * Defines boolean operations to be applied on ASTLtrait, also applicable between two integer
 * Internally, within ASTB integers without consideration for Unsigned, or Signed are used,
 * this avoids codes duplication, and allows to introduce fundefs as vals.
 * However, when applied, only Signed or Unsigned UI must be used, (nameI=repr[I] is not implicit)
 * and it is guaranteed that
 * unsigned (resp. signed) are combined with unsigned (resp. signed) and produce unsigned (resp. signed)
 */
trait MyAstlBoolOp[L <: Locus, R <: Ring] {
  this: ASTLt[L, R] =>
  /*
   * In order to obtain covariance, we would need to introduc types L,U
   *   def &#94;[U >: R <: Ring ](that: ASTLscal[L,U])(implicit m: repr[L],n:repr[U]): ASTL[L, U] =    {      val res = ring match {
   * case B() => Binop(xorB, this.asInstanceOf[ASTLscal[L, B]], that.asInstanceOf[ASTLscal[L, B]],m,repr.nomB)
   * case _   => Binop(xorUISI.asInstanceOf[Fundef2[R,U,U]], this , that ,m,n)
   * }; res.asInstanceOf[ASTL[L, U]]    }
   */
  def |(that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = or(this, that)
  def &(that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = and(this, that)
  def ^(that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = xor(this, that)
  def unary_~(implicit m: repr[L], n: repr[R]): ASTL[L, R] = neg(this)
}
/** Integer spatial operators:  we cannot directly check the type constraint R<:I, ( clash with ASTLs, but we can impose that U<:I and U>:R,  which implies that R<:I*/
trait MyOpInt2[L <: Locus, R <: Ring] {
  this: ASTLt[L, R] =>
  /** adds does not imposes all the operands to be equal type (SI, or UI), no message is given, but compilation fails due to lack of implicit repr[I] */
  def +[U >: R <: I](that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = add(this, that)


  /** minus  must convert UI to SI. */
  def -[U >: R <: I](that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, SI] = ring match {
    case SI() => add[L, SI](this.asInstanceOf[ASTL[L, SI]], -that)
    case UI() => add[L, SI](uItoSIL(this.asInstanceOf[ASTL[L, UI]]), -uItoSIL(that.asInstanceOf[ASTL[L, UI]]))
  }


  //  def unary_-(implicit m: repr[L]): ASTLt[L, SI] = { ASTL.Unop(opp.asobtainInstanceOf[Fundef1[R, SI]], this, m, repr.nomSI) }
  def unary_-(implicit m: repr[L], n: repr[R]): ASTLt[L, SI] = opp(this)

  /** If arguments are  unsigned, we must first convert it to signed */
  def <[U >: R <: I](that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, B] = ring match {
    case SI() => lt2[L](this.asInstanceOf[ASTLt[L, SI]], that.asInstanceOf[ASTLt[L, SI]])
    case UI() => lt2[L](uItoSIL(this.asInstanceOf[ASTLt[L, UI]]), uItoSIL(that.asInstanceOf[ASTLt[L, UI]]))
  }

  //def <[U >: R <: SI](that: ASTLt[L, SI])(implicit m: repr[L], n: repr[SI]): ASTL[L, B] = lt2[L](this.asInstanceOf[ASTLt[L,SI]], that)
  def >[U >: R <: I](that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, B] = ring match {
    case SI() => lt2[L](that.asInstanceOf[ASTLt[L, SI]], this.asInstanceOf[ASTLt[L, SI]])
    case UI() => lt2[L](uItoSIL(that.asInstanceOf[ASTLt[L, UI]]), uItoSIL(this.asInstanceOf[ASTLt[L, UI]]))
  }
}
