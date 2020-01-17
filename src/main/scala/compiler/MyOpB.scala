package compiler

import compiler.AST._
import compiler.ASTB._
import compiler.ASTBfun._
/**Defines boolean operations to be applied on ASTLtrait, also applicable between two integer*/
trait MyOpIntB[+R <: Ring] { this: ASTBt[R] =>
  def +[U >: R <: I](that: ASTBt[U])(implicit n: repr[U]): ASTBt[U] = new Call2(addUISI.asInstanceOf[Fundef2[R, U, U]], this, that)(n) with ASTBt[U]
  def unary_- : ASTBt[R] = new Call1(oppSI.asInstanceOf[Fundef1[R, SI]], this)(repr.nomSI)with ASTBt[SI].asInstanceOf[ASTBt[R]]
  def -[U >: R <: SI](that: ASTBt[U])(implicit n: repr[U]): ASTBt[U] = new Call2(addUISI.asInstanceOf[Fundef2[R, U, U]], this, -that)(n) with ASTBt[U]
}

/**The need for covariance prevents us for verifying that U=R using the scala type system. 
 * We could may be pass other implicit variables! */
  
trait MyOpB[+R <: Ring] {
  this: ASTBt[R] =>
    def ^[U >: R <: Ring ](that: ASTBt[U])(implicit  n:repr[U]) : ASTBt[U]  = {
    val res = ring match {
      case B() => Xor(this.asInstanceOf[ASTBt[B]], that.asInstanceOf[ASTBt[B]])(repr.nomB).asInstanceOf[ASTBt[R]]
      case _   => new Call2(xorI.asInstanceOf[Fundef2[R,U,U]], this , that )(n) with ASTBt[U]
    }; res.asInstanceOf[ASTBt[R]]
  }
    def &[U >: R <: Ring ](that: ASTBt[U])(implicit  n:repr[U]) : ASTBt[U] = {
    val res = ring match {
      case B() => And(this.asInstanceOf[ASTBt[B]], that.asInstanceOf[ASTBt[B]])(repr.nomB).asInstanceOf[ASTBt[R]]
      case _   => new Call2(andI.asInstanceOf[Fundef2[R,U,U]], this , that)(n) with ASTBt[U]
    }; res.asInstanceOf[ASTBt[R]]
  }
   def |[U >: R <: Ring ](that: ASTBt[U])(implicit  n:repr[U]) : ASTBt[U] = {
    val res = ring match {
      case B() => Or(this.asInstanceOf[ASTBt[B]], that.asInstanceOf[ASTBt[B]])(repr.nomB).asInstanceOf[ASTBt[R]]
      case _   => new Call2(orI.asInstanceOf[Fundef2[R,U,U]], this , that)(n) with ASTBt[U]
    }; res.asInstanceOf[ASTBt[R]]
  }
} 