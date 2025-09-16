package compiler

import AST._
import ASTL._
import repr._
import Circuit._
import dataStruc.DagNode._

import scala.collection._
import ASTBfun.ASTBg
import compiler.ASTLt.ConstLayer
import compiler.VarKind.{LayerField, MacroField, ParamD, ParamRR}
import dataStruc.Named

import scala.collection.immutable.HashSet


/**
 * Adds boolean spatial operator to AST of spatial types
 * Also used to bridge the gap with AST. ASTL is inheriting from ASTLt,
 * an ASTL is therefore a more specific instance of ASTLt which  makes use of the catalog of ASTL's contructors.
 * ASTLtrait = AST + ASTL, therefore we should process them separately with a preliminary match, at the level of ASTLtrait.
 * ASTL's constructor uses ASTLtrait for children in order to incorporate AST's nodes.
 * ASTLt dentifies AST corresponding to int or bool, plus a locus, which excludes those obtained with cons
 */

/**
 * Class use to collect information computed by the align "visitor"
 *
 * @param c    a possible cycle constraint or align constraint from another zone.
 * @param si   new affect instructions for shift
 * @param algn alignement on input variables
 */
class Result(var c: Option[Constraint], var si: iTabSymb2[Affect[_]], var algn: iTabSymb2[Array[Int]]) {}

object Result {
  def apply() = new Result(None, immutable.HashMap.empty, immutable.HashMap.empty)
}

trait ASTLt[L <: Locus, R <: Ring] extends AST[(L, R)] with MyAstlBoolOp[L, R] with MyOpInt2[L, R] {
  self: AST[(L, R)] =>

  def locus: L = mym.name._1

  def ring: R = mym.name._2

  /** @return tabulation for printing instructions returning type T */
  override def tabulations = locus.tabul

  def extendMeDirect(n: Int): ASTLt[L, R] =
    ASTLfun.extend[L, R](n, this)(new repr(locus), new repr(ring))

  /** first go get the unique grand child having same bit size */
  def extendMeOld(n: Int): ASTLt[L, R] = {
    var tooSmallBitSize = this
    var candidateForExtend: Set[ASTLg] = HashSet()
    do {
      candidateForExtend = tooSmallBitSize.childSameBitSize
      if (candidateForExtend.size == 1)
        tooSmallBitSize = candidateForExtend.head.asInstanceOf[ASTLt[L, R]]
    }
    while (candidateForExtend.size == 1)

    ASTLfun.extend[L, R](n, this)(new repr(locus), new repr(ring))
  }

  def extendMe(n: Int): ASTLt[L, R] = extendMeDirect(n)

  def childSameBitSize: Set[ASTLg] = HashSet()
  def isRedop: Boolean = false
  def isBinopEdge: Boolean = false
  def isElt:Boolean=false
  def isSend: Boolean = false
  /**
   * @param usedTwice dags which are used twice, or which need to be affected for some other reason.
   * @param idRepr    :id of representant of the equivalence class with respect to equal on case class hierarchy
   * @return transformed tree  with preserved L,R type, for type checking consistency
   *         where delayed are removed,
   *         and expression usedTwice are replaced by read.
   *         generates ASTs such as READ, but implementing ASTLt by creating them using "with ASTLt"
   *         transformation is applied on the whole tree, so subtree verifying usedTwice will
   *         form an independant family */
  override def setReadNodeRemoveDelayed(usedTwice: AstPred, idRepr: Map[AST[_], String]): ASTLt[L, R] = {
    val newD: ASTLt[L, R] = if (usedTwice(this)) new Read[(L, R)](idRepr(this))(mym) with ASTLt[L, R]
    else this match {
      case a: ASTL[L, R] =>
        a.propagateASTL((d: ASTLt[L, R]) => d.setReadNodeRemoveDelayed(usedTwice, idRepr))
      case _ => this.asInstanceOf[AST[_]] match {
        //  case Param(_) => new Read[(L, R)]("p" + idRepr(this))(mym) with ASTLt[L, R]
        case u@Param(_) => new Read[(L, R)]("p" + u.nameP)(mym) with ASTLt[L, R]
        //just revu
        case l: Layer[_] => new Read[(L, R)](Named.lify(idRepr.getOrElse(this, name)))(mym) with ASTLt[L, R]
        case Read(_) => this //throw new RuntimeException("Deja dedagifié!")
        case Delayed(arg) => //arg.asInstanceOf[ASTLt[L, R]].propagate(rewrite)
          arg().asInstanceOf[ASTLt[L, R]].setReadNodeRemoveDelayed(usedTwice, idRepr /* + (arg()->name)*/) //the useless delayed node is supressed
        case _ => this.propagate((d: AST[(L, R)]) => d.setReadNodeRemoveDelayed(usedTwice, idRepr))
      }
    }
    if (idRepr.contains(this))
      newD.setName(idRepr(this))
    //else throw new Exception("no name"));
    newD //.asInstanceOf[ASTLt[L, R]]
  }

  /**
   *
   * @param src    name of an idenfier
   * @param target name of an idenfier
   * @return same tree except target is replaced by src   */
  def replaceBy(src: String, target: String): ASTLt[L, R] = {
    val rewrite: rewriteASTLt[L, R] = (d: ASTLt[L, R]) => d.replaceBy(src: String, target: String)
    val newD: ASTLt[L, R] = this match {
      case a: ASTL[L, R] => a.propagateASTL(rewrite)
      case _ => this.asInstanceOf[AST[_]] match {
        case Read(s) => if (s.equals(src)) new Read[(L, R)](target)(mym) with ASTLt[L, R] else this
        case _ => this //.propagate((d: AST[(L, R)]) => d.replaceBy(src,target))
      }
    }
    newD.asInstanceOf[ASTLt[L, R]]
  }

  /**
   *
   * @param g rewriting AST
   * @return this is rewritten by applying g recursively, exept on arity 0 nodes, and regenerating ASTLt traint
   */
  def propagate(g: rewriteAST[(L, R)]): ASTLt[L, R] = { //to allow covariance on R, second argument of bij2 is l
    val m = mym.asInstanceOf[repr[(L, R)]]
    val newThis = this.asInstanceOf[AST[_]] match {
      case u: Layer[_] => this
      case Read(_) => this

      case Param(_) => this
      case Taail(a) => new Taail[(L, R)](g(a.asInstanceOf[AST[(L, R)]]).asInstanceOf[AST[(Any, (L, R))]])(m) with ASTLt[L, R]
      case Heead(a) => new Heead[(L, R)](g(a.asInstanceOf[AST[(L, R)]]).asInstanceOf[AST[((L, R), Any)]])(m) with ASTLt[L, R]
      case Call1(f, a) => new Call1(f.asInstanceOf[Fundef1[Any, (L, R)]], g(a.asInstanceOf[AST[(L, R)]]))(m) with ASTLt[L, R]
      case Call2(f, a, a2) => new Call2(f.asInstanceOf[Fundef2[Any, Any, (L, R)]], g(a.asInstanceOf[AST[(L, R)]]),
        g(a2.asInstanceOf[AST[(L, R)]]))(m) with ASTLt[L, R]
      case Call3(f, a, a2, a3) => new Call3(
        f.asInstanceOf[Fundef3[Any, Any, Any, (L, R)]],
        g(a.asInstanceOf[AST[(L, R)]]).asInstanceOf[AST[Any]], g(a2.asInstanceOf[AST[(L, R)]]).asInstanceOf[AST[Any]],
        g(a3.asInstanceOf[AST[(L, R)]]).asInstanceOf[AST[Any]])(m) with ASTLt[L, R]
      case _ => throw new RuntimeException("ciel ")
    }
    newThis.setName(this.name);
    newThis
  }


  /**
   * @param nbitLB   Stores number of bits of subfields.
   * @param newTSymb The symbol table with number of bits
   * @return number of bits needed to store the expression this
   *         using  mutable structures, that have  been previously updated.n
   *         this is an arity 0 AST node*/
  def newNbitAST(nbitLB: AstMap[Int], newTSymb: TabSymb[InfoNbit[_]]): Int =
    this.asInstanceOf[AST[_]] match {
      case Param(s) => newTSymb(s).nb
      case Read(s) => newTSymb(s).nb
      case t: Layer[_] => t.nbit
    }

  /**
   * * @param cur The current programm
   * * @param nbitLB Stores number of bits of subfields.
   * * @param tSymb The symbol table with number of bits
   * * @param newFuns Functions generated
   * * @return Expression rewritten so as to include Extend where necessary.
   *
   */
  def bitIfyAndExtend(cur: DataProg[InfoType[_]], nbitLB: AstMap[Int], newtSymb: TabSymb[InfoNbit[_]]): ASTLt[L, R] = {
    val newThis: ASTLt[L, R] = this.propagate((d: AST[(L, R)]) => d.asInstanceOf[ASTLt[L, R]].bitIfyAndExtend(cur, nbitLB, newtSymb))
    nbitLB += (newThis -> newThis.newNbitAST(nbitLB, newtSymb))
    newThis.setName(this.name);
    newThis //.asInstanceOf[ASTLt[L, R]]
  }

  /** @return true if the expression is only a concatenation or broadcast of elements   */
  def justConcatsorBroadcast: Boolean = this match {
    case _: EmptyBag[_] => true
    case _ => false
  }

  /** Defined non empty in ASTL */
  def redExpr = List.empty[AST[_]]
  def binopEdgeExpr = List.empty[AST[_]]

  def align(r: Result, t: TabSymb[InfoNbit[_]]): ASTLt[L, R] =
    this.asInstanceOf[AST[_]] match {
      case Read(s) =>
        r.algn = immutable.HashMap(s -> locus.neutral); this
      case Param(s) =>
        r.algn = immutable.HashMap(s -> locus.neutral); this
      case l: Layer[_] =>
        ; this
    }

  /**
   *
   * @param l locus of the parameter
   * @return a radius of 0 or 1 depending on the locus
   */
  def startRadius(l: Locus) = locus match {
    case V() | T(V(), _) => (0, None)
    case _ => (1, Some(Perimeter())) //from the start, Edge or Face have a radius one.
  }


  /**
   *
   * @param r for computation of all the radius, collect the radius of identifier , plus a modifier making it precise for Edge and Face wether
   *          they are perimeter or radial
   * @param t mutable symbol table to be updated for paramR() to paramRR(Int) where int indicate the radius of result param, so that we
   *          know where to store it.
   * @return radius and modifier of expression
   */
  def radiusify3(r: TabSymb[Int], t: TabSymb[InfoNbit[_]]): (Int, ASTLt[L, R]) =
    (this.asInstanceOf[AST[_]] match {
      case Read(s) => t(s).k match {
        case ParamD() | LayerField(_, _) => 0
        case MacroField() => r(s) //we must have computed it before, and stored it in r
        case ParamRR(1) => 1 //we have generated a variable of radius 1, stored it, and now we read it again. ==> potential pb
        case ParamRR(0) => assert(true, "result of radius O, is that possible?"); 0
        case ParamRR(-1000)  => 0 //-1000 means constant
          //throw new Exception("paramRR-100")
      }

    }, this)

  /*

    def radiusify2(r: TabSymb[Int], t: TabSymb[InfoNbit[_]]): Int =
      this.asInstanceOf[AST[_]] match {
        case Read(s) => t(s).k match {
          case ParamD() | LayerField(_, _) => 0
          case MacroField() => r(s) //we must have computed it before, and stored it in r
        }
      }

    def radiusify(r: TabSymb[(Int, Option[Modifier])], t: TabSymb[InfoNbit[_]]): (Int, Option[Modifier]) =
      this.asInstanceOf[AST[_]] match {
        case Read(s) => t(s).k match {
          case ParamD() => startRadius(locus)
          case MacroField() => r(s) //we should have computed it before, and stored it in r
        }
      }
  */


  /** Only read node are non ASTL nodes and are treated in ASTLt. */
  def unfoldSpace(m: Machine): List[ASTBt[_]] =
    this.asInstanceOf[AST[_]] match {
      /*    case Read(s) => //this part is in fact only used in expression passed to callProc which are allways reads could be factorized
            val r = rpart(mym.asInstanceOf[repr[(L, R)]])
            Locus.deploy(s, this.locus).map(new Read(_)(r) with ASTBt[R])
      */

      case _ =>
        this.locus match {
          case _: S => this.unfoldSimplic(m).toList
          case T(_, _) => this.unfoldTransfer(m).map(_.toList).toList.flatten
        }
    }

  def unfoldSimplic(m: Machine): ArrAst = this.asInstanceOf[AST[_]] match {
    // case t: Layer2[_] =>
    case Read(s) =>
      val r = rpart(mym.asInstanceOf[repr[(L, R)]])
      this.locus.deploy(s).map(new Read[R](_)(r) with ASTBt[R].asInstanceOf[ASTBg])
    case l: Layer[_] => //TODO faut générer des load pas des read
      val s = l.name
      val r = rpart(mym.asInstanceOf[repr[(L, R)]])
      this.locus.deploy(s).map(new Read[R](_)(r) with ASTBt[R].asInstanceOf[ASTBg])

    case _ => throw new RuntimeException("unfoldSpace act only on Reads  for ASTL ")
  }

  /**
   *
   * @param m specifies how communications are implemented and compiled
   * @return an array of array of ASTBg
   *         size of first array is arity of source locus, for T[F,E] it is 2
   *         suze if second array is arity of destination locus for T[F,E] it is 3
   *
   */
  def unfoldTransfer(m: Machine): ArrArrAstBg = this.asInstanceOf[AST[_]] match {
    case Read(s) =>
      val T(s1, _) = this.locus;
      val r = rpart(mym.asInstanceOf[repr[(L, R)]])
      s1.sufx.map((suf1: String) => this.locus.sufx.map((suf2: String) =>
        new Read(s + "$" + suf1 + suf2)(r) with ASTBt[R].asInstanceOf[ASTBg]))
    case _ => throw new RuntimeException("unfoldSpace act only on Reads for ASTLt ")
  }

  /** analyse the ASTL to produce its cost"s information */
  def cost(): Cost = {
    this.asInstanceOf[AST[_]] match {
      // case t: Layer2[_] =>
      case Read(s) => Cost(0, true, true)
      case _ => throw new RuntimeException("unfoldSpace act only on Reads  for ASTL ")
    }
  }


}

object ASTLt {
  /**
   *
   * @param nbit integer's number of bits
   * @return integer constant layer, used for testing!
   */
  def constLayerInt[L <: Locus, R <: I](nbit: Int, c: Int)(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = new ConstLayer[L, R](nbit, c.toString)

  /**
   *
   * @return boolean constant layer, used for testing, and implementing circuit border
   */
  def constLayerBool[L <: Locus](init: String)(implicit m: repr[L]): ASTLt[L, B] = new ConstLayer[L, B](1, init)


  /** constant layer. */
  //private[ASTLt]
  class ConstLayer[L <: Locus, R <: Ring](nbit: Int, init: String)
                                         (implicit m: repr[L], n: repr[R]) extends Layer[(L, R)](nbit, init) with ASTLt[L, R] {
    if(init=="def")//si c'est pas des def, elles sont nomée automatique, sinon faut leur donner un nom comme par exemple, defVe
     this.setName(init + m.name.asInstanceOf[Locus].shortName)//on rajoute un suffix qui indique le type spatial (le locus)
    val locName=m.name.asInstanceOf[Locus].shortName
    val next: ASTLt[L, R] = delayedL(this) //yes
  }

}
