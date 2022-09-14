package compiler

import AST._
import ASTL._
import repr._
import Circuit._
import dataStruc.DagNode._

import scala.collection._
import ASTBfun.ASTBg
import dataStruc.Named


/**
 * Adds boolean spatial operator to AST of spatial types
 * Also used to bridge the gap with AST. ASTL is inheriting from ASTLt,
 * an ASTL is therefore a more specific instance of ASTLt which  makes use of the catalog of ASTL's contructors.
 * ASTLtrait = AST + ASTL, therefore we should process them separately with a preliminary match, at the level of ASTLtrait.
 * ASTL's constructor uses ASTLtrait for children in order to incorporate AST's nodes.
 * ASTLt dentifies AST corresponding to int or bool, plus a locus, which excludes those obtained with cons
 */

/**
 *
 * @param c    a possible cycle constraint
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

  def extendMe(n: Int): ASTLt[L, R] =
    ASTL.extend[L, R](n, this)(new repr(locus), new repr(ring))

  def isRedop: Boolean = false


  /**
   * @param usedTwice dags which are used twice, or which need to be affected for some other reason.
   * @param idRepr    :id of representant of the equivalence class with respect to equal on case class hierarchy
   * @return transformed tree  with preserved L,R type, for type checking consistency
   *         where delayed are removed, and expression usedTwice are replaced by read.
   *         generates ASTs such as READ, but implementing ASTLt by creating them using "with ASTLt"
   *         transformation is applied on the whole tree, so subtree verifying usedTwice will form an independant family */
  override def setReadNode(usedTwice: AstPred, idRepr: Map[AST[_], String]): ASTLt[L, R] = {
    val newD: ASTLt[L, R] = if (usedTwice(this)) new Read[(L, R)](idRepr(this))(mym) with ASTLt[L, R]
    else this match {
      case a: ASTL[L, R] =>
        a.propagateASTL((d: ASTLt[L, R]) => d.setReadNode(usedTwice, idRepr))
      case _ => this.asInstanceOf[AST[_]] match {
        case Param(_) => new Read[(L, R)]("p" + idRepr(this))(mym) with ASTLt[L, R]
        case l: Layer[_] => new Read[(L, R)](Named.lify(idRepr(this)))(mym) with ASTLt[L, R]
        case Read(_) => this //throw new RuntimeException("Deja dedagifié!")
        case Delayed(arg) => //arg.asInstanceOf[ASTLt[L, R]].propagate(rewrite)
          arg().asInstanceOf[ASTLt[L, R]].setReadNode(usedTwice, idRepr /* + (arg()->name)*/) //the useless delayed node is supressed
        case _ => this.propagate((d: AST[(L, R)]) => d.setReadNode(usedTwice, idRepr))
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
        case Read(src) => new Read[(L, R)](target)(mym) with ASTLt[L, R]
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
   * @param nbitLB Stores number of bits of subfields.
   * @param tSymb  The symbol table with number of bits
   * @return number of bits needed to store the expression this
   *         using  mutable structures, that have  been previously updated.n
   *         this is an arity 0 AST node*/
  def newNbitAST(nbitLB: AstMap[Int], tSymb: TabSymb[InfoNbit[_]]): Int =
    this.asInstanceOf[AST[_]] match {
      case Param(s) => tSymb(s).nb
      case Read(s) => tSymb(s).nb
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
  def bitIfyAndExtend(cur: DataProg[InfoType[_]], nbitLB: AstMap[Int], tSymb: TabSymb[InfoNbit[_]]): ASTLt[L, R] = {
    val newThis: ASTLt[L, R] = this.propagate((d: AST[(L, R)]) => d.asInstanceOf[ASTLt[L, R]].bitIfyAndExtend(cur, nbitLB, tSymb))
    nbitLB += (newThis -> newThis.newNbitAST(nbitLB, tSymb))
    newThis.setName(this.name);
    newThis //.asInstanceOf[ASTLt[L, R]]
  }

  /** @return true if the expression is only a concatenation of elements   */
  def justConcats: Boolean = this match {
    case _: EmptyBag[_] => true
    case _ => false
  }

  /** Defined non empty in ASTL */
  def redExpr = List.empty[AST[_]]


  def align(r: Result, t: TabSymb[InfoNbit[_]]): ASTLt[L, R] = this.asInstanceOf[AST[_]] match {
    case Read(s) => r.algn = immutable.HashMap(s -> locus.neutral); this
    case Param(s) => r.algn = immutable.HashMap(s -> locus.neutral); this
    case l: Layer[_] => ; this
  }


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