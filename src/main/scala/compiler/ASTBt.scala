package compiler

import compiler.AST.{Call1, Call2, Call3, Delayed, Fundef1, Fundef2, Fundef3, Layer2, Param, Read}
import compiler.ASTB.{Tminus1, rewriteASTBt}
import compiler.ASTBfun.ASTBg
import compiler.ASTL.rewriteASTLt
import compiler.Circuit.{AstPred, iTabSymb, iTabSymb2}

import scala.collection.Map

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

        // case _ => (this.propagate((d: AST[R]) => d.asInstanceOf[ASTBt[R]].coalesc(newName).asInstanceOf[AST[R]])).asInstanceOf[ASTBt[R]]
      }
    }
    newD.asInstanceOf[ASTBt[R]]
  }

  /**
   * Important to specify that the L,R type of AST nodes is preserved, for type checking consistency
   * Surprisingly, when building ASTL explicitely, we need to drop the fact that the type is preserved,
   * and go from ASTL[L,R] to ASTLg
   * Transform a Dag of AST into a forest of trees, removes the delayed.
   *
   * @return the Dag where expression used more than once are replaced by read.
   *         generates ASTs such as READ that preserve the implementation of  ASTLscal by using "with"
   */
  def treeIfy2(usedTwice: AstPred, repr: Map[AST[_], String]): ASTBt[R] = {
    val rewrite: rewriteASTBt[R] = (d: ASTBt[R]) => d.treeIfy2(usedTwice, repr)
    val newD: ASTBt[R] = if (usedTwice(this)) new Read[R](repr(this))(mym) with ASTBt[R]
    else this match {
      case a: ASTB[R] => a.propagateASTB(rewrite)
      case _ => this.asInstanceOf[AST[_]] match {
        case Param(_) => new Read[R]("p" + repr(this))(mym) with ASTBt[R]
        case l: Layer2[_] => new Read[R](DataProg.lify(repr(this)))(mym) with ASTBt[R]
        case Read(_) => this //throw new RuntimeException("Deja dedagifié!")
        case Delayed(arg) => //arg.asInstanceOf[ASTLt[L, R]].propagate(rewrite)
          arg().asInstanceOf[ASTBt[R]].treeIfy2(usedTwice, repr) //the useless delayed node is supressed
        case Call1(f, a) => new Call1(f.asInstanceOf[Fundef1[Any, R]], a.asInstanceOf[ASTBg].treeIfy2(usedTwice, repr))(mym) with ASTBt[R]
        case Call2(f, a, a2) => new Call2(f.asInstanceOf[Fundef2[Any, Any, R]],
          a.asInstanceOf[ASTBg].treeIfy2(usedTwice, repr),
          a2.asInstanceOf[ASTBg].treeIfy2(usedTwice, repr))(mym) with ASTBt[R]


      }
    }
    newD.setName(if (repr.contains(this)) repr(this) else this.name);
    newD.asInstanceOf[ASTBt[R]]
  }

}


