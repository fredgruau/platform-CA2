package compiler

import ASTL._
import ASTLfun._
import compiler.AST.Fundef2
import compiler.ASTB.{Concat2, False, Intof, True}
import compiler.ASTBfun.{add, ltUI2}
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
   * In order to obtain covariance, we would need to introduc types L,U   */

  def |(that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = binop(ASTBfun.or(n), this, that)(m, n)

  def &(that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = binop(ASTBfun.and(n), this, that)(m, n)

  def ^(that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = binop(ASTBfun.xor(n), this, that)(m, n)

  def unary_~(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = unop(ASTBfun.neg, this)(m, n)
}
/** Integer spatial operators:  we cannot directly check the type constraint R<:I, ( clash with ASTLs, but we can impose that U<:I and U>:R,  which implies that R<:I*/
trait MyOpInt2[L <: Locus, R <: Ring] {
  this: ASTLt[L, R] =>
  /** adds does not imposes all the operands to be equal type (SI, or UI), no message is given, but compilation fails due to lack of implicit repr[I] */

  private def add[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = {
    binop(ASTBfun.add(n).asInstanceOf[Fundef2[R, R, R]], arg1, arg2)(m, n)
  }

  def +[U >: R <: I](that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = binop(ASTBfun.add(n), this, that)(m, n)

  /** It is not possible to impose R<:I for staying compatible with ASTBt[R<:Ring] */
  private def concat2[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = {
    binop(ASTBfun.concat2(n).asInstanceOf[Fundef2[R, R, R]], arg1, arg2)(m, n)
  }

  def ::[U >: R <: I](that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = concat2(this, that)


  /** minus  must convert UI to SI which adds an extra bit. */
  def -[U >: R <: I](that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, SI] = ring match {
    case SI() => add[L, SI](this.asInstanceOf[ASTLt[L, SI]], -that)
    case UI() => add[L, SI](uI2SIL(this.asInstanceOf[ASTL[L, UI]]), -uI2SIL(that.asInstanceOf[ASTL[L, UI]]))
  }


  //  def unary_-(implicit m: repr[L]): ASTLt[L, SI] = { ASTL.Unop(opp.asobtainInstanceOf[Fundef1[R, SI]], this, m, repr.nomSI) }
  def unary_-(implicit m: repr[L], n: repr[R]): ASTLt[L, SI] = opp(this.asInstanceOf[ASTLt[L, SI]])

  /** If arguments are  unsigned, we must first convert it to signed */
  def <[U >: R <: I](that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, B] = lt2(this, that)
  /*
   ring match {
   case SI() => lt2[L](this.asInstanceOf[ASTLt[L, SI]], that.asInstanceOf[ASTLt[L, SI]])

   case UI() =>  ltUI2(this.asInstanceOf[ASTLt[L, UI]], that.asInstanceOf[ASTLt[L, UI]])
 //  case UI() => lt2[L](uItoSIL(this.asInstanceOf[ASTLt[L, UI]]), uItoSIL(that.asInstanceOf[ASTLt[L, UI]]))
 }*/

  //def <[U >: R <: SI](that: ASTLt[L, SI])(implicit m: repr[L], n: repr[SI]): ASTL[L, B] = lt2[L](this.asInstanceOf[ASTLt[L,SI]], that)
  /*  def >[U >: R <: I](that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, B] = ring match {
      case SI() => lt2[L,R](that.asInstanceOf[ASTLt[L, SI]], this.asInstanceOf[ASTLt[L, SI]])
      case UI() => lt2[L,R](uItoSIL(that.asInstanceOf[ASTLt[L, UI]]), uItoSIL(this.asInstanceOf[ASTLt[L, UI]]))
    }*/

  def >[U >: R <: I](that: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, B] = lt2(that, this)
}
