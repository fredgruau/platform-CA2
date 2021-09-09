package compiler

import compiler.AST._
import compiler.ASTL._
import compiler.repr._
import compiler.Circuit._
import scala.collection._


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
 * @param si   shift instruction
 * @param algn alignement on input variables
 */
class Result(var c: Option[Constraint], var si: iTabSymb2[ShiftInstr], var algn: iTabSymb2[Array[Int]]) {}

object Result {
  def apply() = new Result(None, immutable.HashMap.empty, immutable.HashMap.empty)
}

trait ASTLt[L <: Locus, R <: Ring] extends AST[(L, R)] with MyOp[L, R] with MyOpInt2[L, R] {
  self: AST[(L, R)] =>
  def locus: L = mym.name._1

  def ring: R = mym.name._2

  def extendMe(n: Int): ASTLt[L, R] = ASTL.extend(n, this)(new repr(locus), new repr(ring))

  /**
   * Important to specify that the L,R type of AST nodes is preserved, for type checking consistency
   * Surprisingly, when building ASTL explicitely, we need to drop the fact that the type is preserved,
   * and go from ASTL[L,R] to ASTLg
   * Transform a Dag of AST into a forest of trees, removes the delayed.
   *
   * @return the Dag where expression used more than once are replaced by read.
   *         generates ASTs such as READ that preserve the implementation of  ASTLscal by using "with"
   */
  override def deDag(usedTwice: immutable.HashSet[AST[_]], repr: Map[AST[_], AST[_]],
                     replaced: Map[AST[_], AST[_]]): ASTLt[L, R] = {
    val newD = if (usedTwice.contains(this)) new Read[(L, R)](repr(this).name)(mym) with ASTLt[L, R]
    else if (replaced.contains(this)) replaced(this).deDag(usedTwice, repr, replaced)
    else this match {
      case a: ASTL[_, _] =>
        if (a.isInstanceOf[Layer[_, _]])
          new Read[(L, R)]("l" + repr(this).name)(mym) with ASTLt[L, R]
        else a.propagateASTL((d: ASTLt[L, R]) => d.deDag(usedTwice, repr, replaced))
      case _ => this.asInstanceOf[AST[_]] match {
        case Param(_) => new Read[(L, R)]("p" + repr(this).name)(mym) with ASTLt[L, R]
        case Read(_) => throw new RuntimeException("Deja dedagifié!")
        case _ => this.propagate((d: AST[(L, R)]) => d.deDag(usedTwice, repr, replaced))
      }
    }
    newD.setName(this.name);
    newD.asInstanceOf[ASTLt[L, R]]
  }

  N

  override def treeIfy(usedTwice: AstPred, repr: Map[AST[_], String]): ASTLt[L, R] = {
    val rewrite: rewriteASTLt[L, R] = (d: ASTLt[L, R]) => d.treeIfy(usedTwice, repr)
    val newD: ASTLt[L, R] = if (usedTwice(this)) new Read[(L, R)](repr(this))(mym) with ASTLt[L, R]
    else this match {
      case a: ASTL[L, R] =>
        if (a.isInstanceOf[Layer[_, _]])
          new Read[(L, R)]("l" + repr(this))(mym) with ASTLt[L, R]
        else a.propagateASTL(rewrite)
      case _ => this.asInstanceOf[AST[_]] match {
        case Param(_) => new Read[(L, R)]("p" + repr(this))(mym) with ASTLt[L, R]
        case Read(_) => this //throw new RuntimeException("Deja dedagifié!")
        case Delayed(arg) => arg().asInstanceOf[ASTLt[L, R]] //the useless delayed node is supressed
        case _ => this.propagate((d: AST[(L, R)]) => d.treeIfy(usedTwice, repr))
      }
    }
    newD.setName(repr(this));
    newD.asInstanceOf[ASTLt[L, R]]
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
      case u: Layer2[_] => this
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

  //
  //  /** @param nbitLB : computes the #bit of all the ASTL sub expressions, there can be several.   */
  //  override def nbit(cur: ProgData1[_], nbitLB: AstField[Int], tSymb: TabSymb[InfoNbit[_]], newFuns: TabSymb[ProgData2]): ASTLt[L, R] = {
  //    val newThis = this.propagate((d: AST[(L, R)]) => d.nbit(cur, nbitLB, tSymb, newFuns))
  //    nbitLB += (newThis -> newThis.newNbitAST(nbitLB, tSymb, newFuns))
  //    newThis.setName(this.name);
  //    newThis //.asInstanceOf[ASTLt[L, R]]
  //  }

  /**
   * * @param cur The current programm
   * * @param nbitLB Stores number of bits of subfields.
   * * @param tSymb The symbol table with number of bits
   * * @param newFuns Functions generated
   * * @return Expression rewritten so as to include Extend where necessary.
   *
   */
  override def bitIfy(cur: DataProg[_, InfoType[_]], nbitLB: AstField[Int], tSymb: TabSymb[InfoNbit[_]], newFuns: TabSymb[DataProg[_, InfoNbit[_]]]): ASTLt[L, R] = {
    val newThis = this.propagate((d: AST[(L, R)]) => d.bitIfy(cur, nbitLB, tSymb, newFuns))
    nbitLB += (newThis -> newThis.newNbitAST2(nbitLB, tSymb, newFuns))
    newThis.setName(this.name);
    newThis //.asInstanceOf[ASTLt[L, R]]
  }

  def justConcats: Boolean = this match {
    case _: EmptyBag[_] => true
    case _ => false
  }

  /** Defined non empty in ASTL */
  def redExpr = List.empty[AST[_]]

  def align(cs: TabConstr, v: String): iTabSymb[Array[Int]] = this.asInstanceOf[AST[_]] match {
    case Read(s) => immutable.HashMap(s -> locus.neutral)
    case Param(s) => immutable.HashMap(s -> locus.neutral)
  }

  /**
   *
   * @return tree with some id being replaced by shifted version,
   *         cycle constraint, instruction setting the shifted version, alignement with respect to used variables.
   */
  def align2: (ASTLt[_, _], Option[Constraint], iTabSymb2[ShiftInstr], iTabSymb2[Array[Int]]) = this.asInstanceOf[AST[_]] match {
    case Read(s) => (this, None, immutable.HashMap.empty, immutable.HashMap(s -> locus.neutral))
    case Param(s) => (this, None, immutable.HashMap.empty, immutable.HashMap(s -> locus.neutral))
    case l: Layer2[_] => (this, None, immutable.HashMap.empty, immutable.HashMap.empty)
  }

  def align3(r: Result): ASTLt[L, R] = this.asInstanceOf[AST[_]] match {
    case Read(s) => r.algn = immutable.HashMap(s -> locus.neutral); this
    case Param(s) => r.algn = immutable.HashMap(s -> locus.neutral); this
    case l: Layer2[_] => ; this
  }


  /** Only read node are non ASTL nodes and are treated in ASTLt. */
  def unfoldSpace(m: Machine): List[ASTBt[_]] =
    this.asInstanceOf[AST[_]] match {
      case Read(s) =>
        val r = rpart(mym.asInstanceOf[repr[(L, R)]])
        Locus.deploy(s, this.locus).map(new Read(_)(r) with ASTBt[R])
      //      case l: Layer2[_] =>
      //        val r = rpart(mym.asInstanceOf[repr[(L, R)]])
      //        Locus.deploy("totoLayer", this.locus).map(new Read(_)(r) with ASTBt[R])

      case _ => this.locus match {
        case _: S => this.unfoldSimplic(m).toList
        case T(_, _) => this.unfoldTransfer(m).map(_.toList).toList.flatten
      }
    }

  def unfoldSimplic(m: Machine): ArrAst = this.asInstanceOf[AST[_]] match {
    // case t: Layer2[_] =>
    case Read(s) =>
      val r = rpart(mym.asInstanceOf[repr[(L, R)]])
      this.locus.sufx.map((suf: String) => new Read[R](s + "$" + suf)(r) with ASTBt[R].asInstanceOf[ASTBt[_ <: Ring]])
    case l: Layer2[_] =>
      val s = l.name
      val r = rpart(mym.asInstanceOf[repr[(L, R)]])
      this.locus.sufx.map((suf: String) => new Read[R](s + "$" + suf)(r) with ASTBt[R].asInstanceOf[ASTBt[_ <: Ring]])

    case _ => throw new RuntimeException("unfoldSpace act only on Reads  for ASTL ")
  }

  def unfoldTransfer(m: Machine): ArrArrAst = this.asInstanceOf[AST[_]] match {
    case Read(s) =>
      val T(s1, _) = this.locus;
      val r = rpart(mym.asInstanceOf[repr[(L, R)]])
      s1.sufx.map((suf1: String) => this.locus.sufx.map((suf2: String) => new Read(s + "$" + suf1 + suf2)(r) with ASTBt[R].asInstanceOf[ASTBt[_ <: Ring]]))
    case _ => throw new RuntimeException("unfoldSpace act only on Reads for ASTLt ")
  }

}