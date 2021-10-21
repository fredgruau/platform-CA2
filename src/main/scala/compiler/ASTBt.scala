package compiler

import compiler.AST.{Call1, Call2, Call3, Fundef1, Fundef2, Fundef3, Read}
import compiler.ASTB.{Tminus1, rewriteASTBt}
import compiler.Circuit.{iTabSymb, iTabSymb2}

/** Identifies AST corresponding to int or bool, excludes those obtained with cons */
trait ASTBt[+R <: Ring] extends AST[R] with MyOpB[R] with MyOpIntB[R] {
  self: AST[R] =>
  def ring: R = mym.name

  def detm1ise: ASTBt[R] = this match {
    case Tminus1(e) => e
    case _ => this
  } //throw new Exception("it does not begin by tm1, and it should")}
  /** sinon y a une erreur du compilo scala empty modifier. */
  val u = 3;
  val v = 3

  /**
   *
   * @param newName correspondance towards scalar names
   * @return same tree except target is replaced by src   */

  def coalesc(newName: iTabSymb[String]): ASTBt[R] = {
    val rewrite: rewriteASTBt[R] = (d: ASTBt[R]) => d.coalesc(newName)
    val newD: ASTBt[R] = this match {
      case a: ASTB[R] => a.propagateASTB(rewrite)
      case _ => this.asInstanceOf[AST[_]] match {
        case Read(x) =>
          if (!newName.contains(x)) this
          else new Read[R](newName(x))(mym) with ASTBt[R]
        //the copy calls done by AST'propagate will preserve the trait ASTBt[R]===>NOT
        case Call1(f, a) => new Call1(f.asInstanceOf[Fundef1[Any, R]], a.asInstanceOf[ASTBt[_]].coalesc(newName))(mym) with ASTBt[R]
        case Call2(f, a, a2) => new Call2(f.asInstanceOf[Fundef2[Any, Any, R]],
          a.asInstanceOf[ASTBt[R]].coalesc(newName),
          a2.asInstanceOf[ASTBt[R]].coalesc(newName))(mym) with ASTBt[R]

        case _ => (this.propagate((d: AST[R]) => d.asInstanceOf[ASTBt[R]].coalesc(newName).asInstanceOf[AST[R]])).asInstanceOf[ASTBt[R]]
      }
    }
    newD.asInstanceOf[ASTBt[R]]
  }


}


