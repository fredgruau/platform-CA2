package compiler

import AST._
import ASTB._
import ASTBfun._
import ASTL.neg

/** Defines boolean operations in infix notation, for Bool, Uint, Sint */
trait MyOpIntB[+R <: Ring] {
  this: ASTBt[R] =>
  def +[U >: R <: I](that: ASTBt[U])(implicit n: repr[U]): ASTBt[U] =
    new Call2(addUISI(ring).asInstanceOf[Fundef2[R, U, U]], this, that)(n) with ASTBt[U]
  def unary_- : ASTBt[R] = new Call1(oppSI.asInstanceOf[Fundef1[R, SI]], this)(repr.nomSI) with ASTBt[SI].asInstanceOf[ASTBt[R]]

  //def -[U >: R <: SI](that: ASTBt[U])(implicit n: repr[U]): ASTBt[U] = new Call2(addUISI.asInstanceOf[Fundef2[R, U, U]], this, -that)(n) with ASTBt[U]
  // def -[U >: R <: SI](that: ASTBt[U])(implicit n: repr[U]): ASTBt[U] = new Call2(subSI2.asInstanceOf[Fundef2[R, U, U]], this, that)(n) with ASTBt[U]
  def -[U >: R <: SI](that: ASTBt[U])(implicit n: repr[U]): ASTBt[U] = this + (-that)

  def ::[U >: R <: UISI](that: ASTBt[U])(implicit n: repr[U]): ASTBt[U] = Concat2(this, that)
}

/**The need for covariance prevents us for verifying that U=R using the scala type system. 
 * We could may be pass other implicit variables! */
  
trait MyOpB[+R <: Ring] {
  this: ASTBt[R] =>

  def unary_~ = {
    def negSimplif(exp: ASTBt[B]) = exp match {
      case ASTB.False() => ASTB.True()
      case ASTB.True() => ASTB.False()
      case Neg(exp) => exp
      case _ => Neg(this.asInstanceOf[ASTBt[B]])(repr.nomB).asInstanceOf[ASTBt[B]]
    }

    def negB[R <: Ring](arg: ASTBt[R]): ASTBt[R] = {
      (arg.ring match {
        case B() => negSimplif(arg.asInstanceOf[ASTBt[B]]) // Unop(negB, arg.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
        case SI() => new Call1[SI, SI](negSI, arg.asInstanceOf[Sint]) with Sint //Unop(negSI.asInstanceOf[Fundef1[R, R]], arg, m, n)
        case UI() => new Call1[UI, UI](negUI, arg.asInstanceOf[Uint]) with Uint //Unop(negSI.asInstanceOf[Fundef1[R, R]], arg, m, n)
      }).asInstanceOf[ASTBt[R]]
    }

    negB(this)
  }


  def <[U >: R <: Ring](that: ASTBt[U])(implicit n: repr[B]): ASTBt[B] = {
    ring match {
      case B() => if (this == False() && that == False()) True() else False()
      case SI() => new Call2(ltSI2Mod.asInstanceOf[Fundef2[R, U, B]], this, that)(n) with ASTBt[B] //todo calculer le vrai ltSI2
    }
  }

  def <=[U >: R <: Ring](that: ASTBt[U])(implicit n: repr[B]): ASTBt[B] = {
    ring match {
      case B() => if (this == False() && that == False()) True() else False()
      case SI() => new Call2(leSI2.asInstanceOf[Fundef2[R, U, B]], this, that)(n) with ASTBt[B]
    }
  }

  def ^[U >: R <: Ring](that: ASTBt[U])(implicit n: repr[U]): ASTBt[U] = {
    val res = ring match {
      case B() => ASTB.addXor(this.asInstanceOf[ASTBt[B]], that.asInstanceOf[ASTBt[B]])
      case _ => new Call2(xorUISI(ring).asInstanceOf[Fundef2[R, U, U]], this, that)(n) with ASTBt[U]
    };
    res.asInstanceOf[ASTBt[R]]
  }


  /** we allow and between a boolean and an integer, called andLBtoRUI/SI */
  def &[U >: R <: Ring](that: ASTBt[U])(implicit n: repr[U]): ASTBt[U] = {
    val res = ring match {
      case B() =>
        that.ring match {
          case B() => ASTB.addAnd(this.asInstanceOf[ASTBt[B]], that.asInstanceOf[ASTBt[B]])
          case SI() => new Call2(andLBtoRSI.asInstanceOf[Fundef2[R, U, U]], this, that)(n) with ASTBt[U]
          case UI() => new Call2(andLBtoRUI.asInstanceOf[Fundef2[R, U, U]], this, that)(n) with ASTBt[U]
        }
      case _ => new Call2(andUISI(ring).asInstanceOf[Fundef2[R, U, U]], this, that)(n) with ASTBt[U]
    };
    res.asInstanceOf[ASTBt[R]]
  }

   def |[U >: R <: Ring ](that: ASTBt[U])(implicit  n:repr[U]) : ASTBt[U] = {
     val r = ring
     val res = r match {
      case B() => ASTB.addOr(this.asInstanceOf[ASTBt[B]], that.asInstanceOf[ASTBt[B]])
      case _ => new Call2(orUISI(ring).asInstanceOf[Fundef2[R, U, U]], this, that)(n) with ASTBt[U]
    }; res.asInstanceOf[ASTBt[R]]
  }
} 