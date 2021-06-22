package compiler

import compiler.AST._
import compiler.InfoType._
import compiler.Instr._
import compiler.Locus.{deploy, _}
import compiler.UsrInstr._
import compiler.VarKind._
import dataStruc.{Align, DagNode, SetInput}
import compiler.Circuit._

import scala.language.postfixOps
import scala.collection._
import scala.collection.immutable.HashSet

/** Instruction used within the compiler, call, affect. Dag and Union allows to defined ConnectedComp  */
abstract class Instr extends DagNode[Instr] with Align[Instr] with SetInput[Instr] {

  def isReturn: Boolean = this match {
    case CallProc("return", _, _) => true;
    case _ => false
  }

  def exps: List[AST[_]]

  def propagate(id1: rewriteAST2): Instr

  override def aligned = !alignPerm.isEmpty //faut de mefier, ca va pas marcher pour load?
  def useless = false

  /** true for instruction part or Transfer Connected Components */
  def isTransfer: Boolean

  /** @return the locus of expressions, for affectation. */
  def locus: Option[Locus] = None

  def isV = locus.get == V()

  /** to be set if we want to use the Align feature, contains an alignment towards each usedvars of the instr (indexed by the string) */
  var alignPerm: iTabSymb[Array[Int]] = Map.empty

  /*Must return an alignement from this to n.   */
  def neighborAlign(n:  Instr ): Array[Int]={
      if(alignPerm.isEmpty) null
  else if(alignPerm.contains(n.names.head)) //n is a used var of this, so "this" is an element of n.neighbor,
       alignPerm(n.names.head) //neighborAligned(n.names(0))  is an alignement from "this" to n,
    else  if(n.alignPerm.contains( names.head))   //ca doit etre le contraire, i.e. this is a used var of n. we find an alignement from n to "this", we must invert
         Align.invert(n.alignPerm(names.head))
    else throw new RuntimeException(" Not find alignement ") 
  }

  // val exp:AST[T]
  /**@param hd head
   * @param tl and tail  are built, in order to  find out the id of formal parameter passed by results. */
  def buildhdtl(hd: TabSymb[String], tl: TabSymb[String]): Unit = this match {
    case Affect(_, exp) => exp match {
      case Heead(Read(s)) => hd += s -> exp.name
      case Taail(Read(s)) => tl += s -> exp.name
      case _ =>
    }
    case _ =>
  }

  /**
   *
   * @param hd list names associated to head
   * @param tl list of names associated to tail
   * @param t  symbol table
   * @return Replaces instruction of the form Affect(Call ..) expressions, by callProc instructions.
   *         Remove head and tail operations which have become useless, and return instructions.
   */
  def procedurIfy(hd: TabSymb[String], tl: TabSymb[String], t: TabSymb[InfoType[_]]): List[Instr] = {
    /**
     * @param s
     * @return names of ASTL variables, associated to variable of type cons(cons...))
     */
    def subNames(s: String): List[String] = if (hd.contains(s)) hd(s) :: subNames(tl(s)) else List(s)

    this match {
      case Affect(s, exp) => exp match {
        case c: Call[_] =>
          val res = subNames(s)
          //value which are sent through call and retrieved from the procedure, have to be stored
          for (r <- res ::: c.args.toList.map(_.name))
            if (t(r).k == Field()) t += r -> new InfoType(t(r).t, StoredField()); // register the fact that results must be stored.

          List(CallProc(c.f.namef, res, c.args.toList))
        case Taail(_) | Heead(_) => List() //we do not need those any more.
        case _ => List(this)
      }

      case _ => if (this.isReturn) List() else List(this)
    }
  }

  def nbit(cur: ProgData1[_], nbitLB: AstField[Int], tSymb: TabSymb[InfoNbit[_]], newFuns: TabSymb[ProgData2]): Instr = this match {
    case Affect(s, exp) =>
      val newExp = exp.nbit(cur, nbitLB, tSymb, newFuns)
      tSymb += s -> new InfoNbit(cur.tSymbVar(s).t, cur.tSymbVar(s).k, nbitLB(newExp)); Affect(s, newExp).asInstanceOf[Instr]
    case CallProc(f, names, exps) =>
      val newexps = exps.map(_.nbit(cur, nbitLB, tSymb, newFuns))
      val nbitarg = newexps.map(a => nbitLB(a)) //.toList.flatten
      val newnamef = f + nbitarg.map(_.toString).foldLeft("")(_ + "_" + _)
      if (!newFuns.contains(newnamef)) newFuns += (newnamef -> cur.funs(f).nbit(nbitarg)) // re-creates the code of f, taking into account nbitarg.
      val fprog = newFuns(newnamef)
      val nbitResult = fprog.paramR.map(s => fprog.tSymbVar(s).nb) //we get the number of bits of results
      (names zip nbitResult).foreach { sn => tSymb += sn._1 -> new InfoNbit(cur.tSymbVar(sn._1).t, cur.tSymbVar(sn._1).k, sn._2) }
      CallProc(newnamef, names, newexps).asInstanceOf[Instr]
  }

  /**
   *
   * @param cur     The current programm
   * @param nbitLB  Stores number of bits of subfields.
   * @param tSymb   The symbol table with number of bits
   * @param newFuns Functions generated
   * @return The instructions rewritten so as to include Extend where necessary.
   */
  def bitIfy(cur: DataProg[_, InfoType[_]], nbitLB: AstField[Int], tSymb: TabSymb[InfoNbit[_]], newFuns: TabSymb[DataProg[_, InfoNbit[_]]]): Instr = this match {
    case Affect(s, exp) =>
      val newExp = exp.bitIfy(cur, nbitLB, tSymb, newFuns)
      tSymb += s -> new InfoNbit(cur.tSymbVar(s).t, cur.tSymbVar(s).k, nbitLB(newExp));
      Affect(s, newExp).asInstanceOf[Instr]
    case CallProc(f, names, exps) =>
      val newexps = exps.map(_.bitIfy(cur, nbitLB, tSymb, newFuns))
      val nbitarg = newexps.map(a => nbitLB(a)) //.toList.flatten
      val newnamef = f + nbitarg.map(_.toString).foldLeft("")(_ + "_" + _)
      if (sysInstr.contains(f))
      //there is not code to be generated for system calls
        CallProc(f, names, newexps).asInstanceOf[Instr]
      else {
        if (!newFuns.contains(newnamef))
          newFuns += (newnamef -> cur.funs(f).bitIfy(nbitarg))
        // re-creates the code of f, taking into account nbitarg.
        val fprog = newFuns(newnamef)
        val nbitResult = fprog.paramR.map(s => fprog.tSymbVar(s).nb) //we get the number of bits of results
        (names zip nbitResult).foreach { sn => tSymb += sn._1 -> new InfoNbit(cur.tSymbVar(sn._1).t, cur.tSymbVar(sn._1).k, sn._2) }
        CallProc(newnamef, names, newexps).asInstanceOf[Instr]
      }
  }


  // TabSymb[InfoNbit[_]]
  /** we add one (resp. two) suffixes, for simplicial (resp. transfer) variables  */
  def unfoldSpace(m: Machine, tSymb: TabSymb[InfoNbit[_]]): List[Instr] = this match {
    case Affect(v, exp) => // println(exp.toStringTree) ;
      val exp2 = exp.asInstanceOf[ASTLt[_, _]]
      exp2.locus match {
        case s: S => s.sufx.zip(exp2.unfoldSimplic(m)).map({ case (suf, e) => Affect(v + "$" + suf, e) }).toList
        case l@T(s1, _) => s1.sufx.zip(exp2.unfoldTransfer(m)).map({
          case (suf1, t) =>
            l.sufx.zip(t).map({ case (suf2, e) => Affect(v + "$" + suf1 + suf2, e) }).toList
        }).toList.flatten
      }
    case CallProc(f, n, e) => List(CallProc(f, n.flatMap(Instr.deploy(_, tSymb)), e.asInstanceOf[List[ASTLt[_, _]]].flatMap(_.unfoldSpace(m)))) //tSymb(n).t._1
  }

  def align(cs: TabSymb[Constraint]): Unit = alignPerm = a(this).exp.asInstanceOf[ASTLt[_, _]].align(cs, names.head)

}

/**
 * call of a procedure,
 * where several parameters can be passed by result.
 *
 * @param p     procedure's' name
 * @param names resutl's name
 * @param exps  passed as data
 */
case class CallProc(p: String, names: List[String], exps: List[AST[_]]) extends Instr {
  /**
   * @return string shows the results being affected simultaneously
   */
  override def toString: String = pad(names.mkString(","), 25) + "<-" + p + "(" + exps.map(_.toStringTree).mkString(" ") + ")\n"

  //override def toString: String = pad(names.foldLeft(" ")(_ + "," + _).substring(2), 25) + "<-" + p + "(" + exps.map(_.toStringTree).foldLeft(" ")(_ + " " + _) + ")\n"
  def usedVars: HashSet[String] = exps.map(_.symbols).foldLeft(immutable.HashSet.empty[String])(_ | _)

  override def isTransfer: Boolean = throw new RuntimeException("test isTransfer is done only in macro, which do not have CallProc instr. ")

  override def propagate(id1: rewriteAST2): Instr = {
    val newInstr = CallProc(p, names, exps.map((a: AST[_]) => id1(a)))
    newInstr
  }

}

/**
 *
 * @param name    variable computed
 * @param shifted input variable being shifted
 * @param perm    Compute a shift permutation.
 */
case class ShiftInstr(name: String, shifted: String, perm: Array[Int]) extends Instr {
  override def exps: List[AST[_]] = List()

  override def propagate(id1: rewriteAST2): Instr = this

  /** true for instruction part or Transfer Connected Components */
  override def isTransfer: Boolean = true

  /** names of variables modified by instruction. */
  override def usedVars: HashSet[String] = HashSet(shifted)

  override def names: List[String] = List(shifted)
}

case class Affect[+T](name: String, val exp: AST[T]) extends Instr {
  def exps = List(exp)

  val names = List(name);

  override def toString: String = pad(name, 25) + "<-  " + exp.toStringTree + show(locus) +
    (if (alignPerm.isEmpty) "" else alignPerm.map({ case (k, v) => k + " " + v.toList + ";  " })) + "\n"

  private def show(x: Option[Locus]) = x match {
    case Some(s) => "" + s
    case None => ""
  }

  def usedVars: HashSet[String] = exp.symbols

  /**
   * for a non macro affectation of parameter or a Layer creates a useless entry in the memory of the CA
   * because the parameter or the layer is already present in the memory of the CA
   */
  override def useless: Boolean = exp match {
    case _: ASTL.Layer[_, _] => true
    case Param(_) => true
    case _ => false
  }

  /** @return if instruction is ASTLt, returns the locus */
  override def locus: Option[Locus] = exp match {
    case a: ASTLt[_, _] => Some(a.locus)
    case _ => None
  }

  override def isTransfer: Boolean = exp.asInstanceOf[ASTLt[_, _]].locus.isInstanceOf[TT] // || exp.isInstanceOf[Red2[_,_,_]]
  override def propagate(id1: rewriteAST2): Instr = Affect(name, id1(exp))

  /**
   *
   * @param cs
   */
  def align2(cs: TabSymb[Constraint]): Affect[_] = {
    val toto = exp.asInstanceOf[ASTLt[_, _]].align2
    val tree = toto._1
    val algn = toto._4
    val c = toto._2
    val instrs = toto._3
    val newAffect = Affect(name, tree)
    newAffect.alignPerm = algn
    if (c != None) cs.addOne(name -> c.get)
    newAffect
  }

  def align3(cs: TabSymb[Constraint]): Affect[_] = {
    val r = Result()
    val newExp = exp.asInstanceOf[ASTLt[_, _]].align3(r)
    val newAffect = Affect(name, newExp)
    newAffect.alignPerm = r.algn
    if (r.c != None)
      cs.addOne(name -> r.c.get)
    newAffect
  }


}

object Instr {
  val sysInstr = HashSet("return", "bug", "show", "memo")

  /** @param i instruction
   * @return i.asInstanceOf[Affect[_]]*/
  def a(i: Instr): Affect[_] = i.asInstanceOf[Affect[_]]

  def read(s: String, m: repr[(Locus, Ring)]) = new Read(s)(m) with ASTLt[Locus, Ring]

  /** utility used to align instruction when printed */
  def pad(s: String, n: Int): String = s + " " * (n - s.length())

  def apply(s: String, p: ProgData2): Instr = CallProc(s, p.paramR,
    p.paramD.map(x => read(x, repr(p.tSymbVar(x).t).asInstanceOf[repr[(_ <: Locus, _ <: Ring)]])))

  /**
   * @param s name of function
   * @param p the function itself
   * @return call to that function. effective parameter's name, are identical to formal.
   */
  def apply(s: String, p: DataProg[_, InfoNbit[_]]): Instr = {
    val call = CallProc(s, p.paramR, p.paramD.map(x => read(x, repr(p.tSymbVar(x).t).asInstanceOf[repr[(_ <: Locus, _ <: Ring)]])))
    call
  }

  private def deploy(n: String, tSymb: TabSymb[InfoNbit[_]]): List[String] = Locus.deploy(n, tSymb(n).t.asInstanceOf[(_ <: Locus, _)] _1)

  /**
   *
   * @param tsymb
   * @param paramD side effect: will receive the name of the result parameters, in right order
   * @param e      the expression returned incuding possibly Coons, to gather several parameters.
   * @return Instruction Affect of value computed by the function, to resultParameters.
   */
  def affectizeReturn(tsymb: TabSymb[InfoType[_]], paramD: mutable.LinkedHashSet[String], e: AST[_]): List[Instr] = {
    /**
     * @param e of the form Coons(e1,e2)
     * @return Affect of value computed by the function, to resultParameters.
     */
    def process(e: AST[_]): List[Affect[_]] = {
      val already = tsymb.contains(e.name)
      val newName = if (!already || already && tsymb(e.name).k == Field()) e.name else checkName2() //we create another variable to return result, in case it is a layer.
      paramD += newName;
      tsymb += newName -> InfoType(e, ParamR())
      if (already && newName == e.name) List() else List(Affect(newName, e))
    }
    //recursive call because a function can returns several results grouped  together using Coons()
    e match {
      case Coons(e1, e2) => process(e1) ::: affectizeReturn(tsymb, paramD, e2)
      case _ => process(e)
    }
  }
}

/**Instructions generated within the ast that will not be used after dedagification.  */
case class UsrInstr[+T](c: Codop, exp: AST[_]) extends Instr {
  def exps = List(exp)

  def usedVars = immutable.HashSet.empty[String]
  val names = List(); override def toString: String = pad(c.toString.substring(2), 25) + "<-  " + exp.toStringTree

  /**
   * Generate the affect instructions from a memorize, display or bugif instruction.
   *  for display if variable has also been used somewhere else, no affect needs to be generated
   *  @param expFather the expression associated either pictured, debugged or the layer if it is a memorize
   *  @param usedForCompute true if expression is also used in the computation (meaning it has been stored already)
   */
  def affectize(expFather: AST[_], usedForCompute: Boolean, t: TabSymb[InfoType[_]]): Option[Affect[_]] =
    c match {
      case Memorize() =>
        val nbit = expFather.asInstanceOf[ASTL.Layer[_, _]].nbit
        addSymbL(t, expFather, LayerField(nbit)); Some(Affect("l" + expFather.name, exp))
      case Bugif() =>
        if (usedForCompute) throw new RuntimeException("Debug exp is allzero=>not usable for compute")
        val b=t.contains(exp.name)
        addSymb(t, exp, BugifField(expFather.name))
        if (b)  None
        else  Some(Affect(exp.name, exp))   //the bugif has allready been generated, we need to change the varialbe
      case Display() => if (usedForCompute || t.contains(exp.name)) None
      else { addSymb(t, exp, DisplayField(expFather.name, usedForCompute)); Some(Affect(exp.name, exp)) }
    }

  /** true for instruction part or Transfer Connected Components */
  override def isTransfer: Boolean = exp.mym.name.isInstanceOf[TT]

  override def propagate(id1: rewriteAST2): Instr = this
}
object UsrInstr {

  sealed class Codop

  private case class Display() extends Codop;

  def display(e: AST[_]): UsrInstr[_] = new UsrInstr(Display(), e)

  private case class Memorize() extends Codop;

  def memorize(e: AST[_]): UsrInstr[_] = new UsrInstr(Memorize(), e)

  private case class Bugif() extends Codop;

  def bugif(e: AST[_]): UsrInstr[_] = new UsrInstr(Bugif(), e)

  /** used very temporary to store the expression forming the body of a function */
  //case class Result() extends Codop; def result(e: AST[_]): UsrInstr[_] = new UsrInstr(Result(), e)

  //private case class Affect(val name: String) extends Codop{override def toString=name+"\t<-"}; def affect(e: AST[_]): UsrInstr[_] = new UsrInstr(Affect(e.name), e)
}
