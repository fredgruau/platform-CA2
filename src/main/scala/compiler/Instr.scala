package compiler

import compiler.AST._
import compiler.InfoType._
import compiler.Instr._
import compiler.ProgData._
import compiler.UsrInstr._
import compiler.VarKind._

import scala.collection._

/**Instruction used within the compiler, call, affect. Dag and Union allows to defined ConnectedComp  */
abstract class Instr extends Dag[Instr] with Align[Instr] {
  def useless = false; 
  var neighbor: List[Instr] = List.empty; //to be set if we want to use the Dag feature.
  var alignPerm:iTabSymb[Array[Int]]=Map.empty  // to be set if we want to use the Align feature, contains an alignment towards each usedvars of the instr (indexed by the string)
  /*Must return an alignement from this to n.   */
  def neighborAlign(n:  Instr ): Array[Int]={
      if(alignPerm.isEmpty) return null
  else if(alignPerm.contains(n.names(0))) //n is a used var of this, so "this" is an element of n.neighbor, 
       alignPerm(n.names(0)) //neighborAligned(n.names(0))  is an alignement from "this" to n,
    else  if(n.alignPerm.contains( names(0)))   //ca doit etre le contraire, i.e. this is a used var of n. we find an alignement from n to "this", we must invert
         Align.invert(n.alignPerm(names(0)))
    else throw new RuntimeException(" Not find alignement ") 
  }
  /** names of variables modified by instruction.*/
  def usedVars: immutable.HashSet[String]
  def names: List[String]
  // val exp:AST[T]
  /**@hd @tl are build, in order to  find out the id of formal parameter passed by results. */
  def buildhdtl(hd: TabSymb[String], tl: TabSymb[String]): Unit = this match {
    case Affect(s, exp) => exp match {
      case Heead(Read(s)) => hd += s -> exp.name
      case Taail(Read(s)) => tl += s -> exp.name
      case _              =>
    }
    case _ =>
  }

  /**Translate into procedure calls, Remove head and tail operations which have become useless, replace instruction result by affectations. */
  def procedurise(hd: TabSymb[String], tl: TabSymb[String], t: TabSymb[InfoType[_]]): List[Instr] = {
    /**Computes the list of names of ASTL variables, associated to variable of type cons(cons...)) */
    def subNames(s: String): List[String] = if (hd.contains(s)) hd(s) :: subNames(tl(s)) else List(s)
    this match {
      case Affect(s, exp) => exp match {
        case c: Call[_] =>
          val res = subNames(s);
          //value which are sent through call and retrieved from the procedure, have to be stored
          for (r <- res ::: c.args.toList.map(_.name)) if (t(r).k == Field()) t += r -> new InfoType(t(r).t, StoredField()); // register the fact that results must be stored.

          List(CallProc(c.f.namef, res, c.args.toList))
        case Taail(_) | Heead(_) => List() //we do not need those any more.
        case _                   => List(this)
      }
      case _ => List(this)
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
      if (!newFuns.contains(newnamef)) newFuns += (newnamef -> cur.funs(f).nbit(nbitarg).asInstanceOf[ProgData2]) // re-creates the code of f, taking into account nbitarg.
      val fprog = newFuns(newnamef)
      val nbitResult = fprog.paramR.map(s => fprog.tSymbVar(s).nb) //we get the number of bits of results
      (names zip nbitResult).foreach { sn => tSymb += sn._1 -> new InfoNbit(cur.tSymbVar(sn._1).t, cur.tSymbVar(sn._1).k, sn._2) }
      CallProc(newnamef, names, newexps).asInstanceOf[Instr]
  }

  // TabSymb[InfoNbit[_]]
  /**we add one (resp. two) suffixes, for simplicial (resp. transfer) variables  */
  def unfoldSpace(m: Machine, tSymb: TabSymb[InfoNbit[_]]): List[Instr] = this match {
    case Affect(v, exp) => // println(exp.toStringTree) ;
      exp.asInstanceOf[ASTLt[_, _]].locus match {
        case s: S => s.sufx.zip(exp.unfoldSimplic(m)).map({ case (suf, e) => Affect(v +"$"+suf, e) }).toList
        case l @ T(s1, s2) => s1.sufx.zip(exp.unfoldTransfer(m)).map({
          case (suf1, t) =>
            l.sufx.zip(t).map({ case (suf2, e) => Affect(v + "$"+ suf1 + suf2, e) }).toList
        }).toList.flatten
      }
    case CallProc(f, n, e) => List(CallProc(f, n.map(deploy(_, tSymb)).flatten, e.map(_.unfoldSpace(m)).flatten)) //tSymb(n).t._1
  }
  
  def align(cs:TabSymb[immutable.HashSet [Constraint]])={ alignPerm=a(this).exp.align(cs, names(0))  }
}

/**   call of a procedure, where several parameters can be passed by result. Printed shows them as results being affected at the same time  */
case class CallProc(val f: String, val names: List[String], val exps: List[AST[_]]) extends Instr {
  override def toString = pad(names.foldLeft(" ")(_ + "," + _).substring(2), 25) + "<-" + f + "(" + exps.map(_.toStringTree).foldLeft(" ")(_ + " " + _) + ")\n"
  def usedVars = exps.map(_.symbols).foldLeft(immutable.HashSet.empty[String])(_ | _)
};

case class Affect[+T](val name: String, val exp: AST[T]) extends Instr {
  val names = List(name); override def toString = pad(name, 25) + "<-  " + exp.toStringTree   +  alignPerm.map({case(k,v)=> k +" "+ v.toList+";  "})  + "\n"
   
  def usedVars = exp.symbols
  /**
   * for a non macro affectation of parameter or a Layer creates a useless entry in the memory of the CA
   * because the parameter or the layer is already present in the memory of the CA
   */
  override def useless: Boolean = exp match { case l: ASTL.Layer[_, _] => true case Param(_) => true case _ => false }
};

object Instr {
  def a(i:Instr) =i.asInstanceOf[Affect[_]]
  def read(s: String, m: repr[(Locus, Ring)]) = new Read(s)(m) with ASTLt[Locus, Ring]
  /**utility used to align instruction when printed */
  def pad(s: String, n: Int): String = s + " " * (n - s.length())
  def apply(s: String, p: ProgData2): Instr = CallProc(s, p.paramR,
    p.paramD.map(x => read(x, repr(p.tSymbVar(x).t).asInstanceOf[repr[(_ <: Locus, _ <: Ring)]])))

  //new Read[Int](x)))
  //replace the return expression by affectation
  def affectizeReturn(tsymb: TabSymb[InfoType[_]], paramD: mutable.LinkedHashSet[String], e: AST[_]): List[Instr] = {
    def process(e: AST[_]): List[Affect[_]] = {
      val already = tsymb.contains(e.name);
      val newName = if (!already || already && tsymb(e.name).k == Field()) e.name else checkName2 //we create another variable to return result, in case it is a layer.
      paramD += newName; tsymb += newName -> InfoType(e, ParamR()); if (already && newName == e.name) List() else List(Affect(newName, e))
    }
    e match { case Coons(e1, e2) => process(e1) ::: affectizeReturn(tsymb, paramD, e2) case _ => process(e) }

  }
}

/**Instructions generated within the ast that will not be used after dedagification.  */
case class UsrInstr[+T](val c: Codop, val exp: AST[_]) extends Instr {
  def usedVars = immutable.HashSet.empty[String]
  val names = List(); override def toString = pad(c.toString.substring(2), 25) + "<-  " + exp.toStringTree

  /**
   * Generate the affect instructions from a memorize, display or bugif instruction.
   *  for display if variable has also been used somewhere else, no affect needs to be generated
   *  @expfather the expression associated either pictured, debugged or the layer if it is a memorize
   *  @usedForCompute true if expression is also used in the computation (meaning it has been stored already)
   */
  def affectize(expFather: AST[_], usedForCompute: Boolean, t: TabSymb[InfoType[_]]): Option[Affect[_]] =
    c match {
      case Memorize() =>
        val nbit = expFather.asInstanceOf[ASTL.Layer[_, _]].nbit
        addSymbL(t, expFather, LayerField(nbit)); Some(Affect("l" + expFather.name, exp))
      case Bugif() =>
        if (usedForCompute) throw new RuntimeException("Debug exp is allzero=>not usable for compute");
        addSymb(t, exp, BugifField(expFather.name));
        if (t.contains(exp.name))  None  else    Some(Affect(exp.name, exp)) //the bugif has allready been generated, we need to change the varialbe
      case Display() => if (usedForCompute || t.contains(exp.name)) None
      else { addSymb(t, exp, DisplayField(expFather.name, usedForCompute)); Some(Affect(exp.name, exp)) }
    }
}
object UsrInstr {
  sealed class Codop
  private case class Display() extends Codop; def display(e: AST[_]): UsrInstr[_] = new UsrInstr(Display(), e)
  private case class Memorize() extends Codop; def memorize(e: AST[_]): UsrInstr[_] = new UsrInstr(Memorize(), e)
  private case class Bugif() extends Codop; def bugif(e: AST[_]): UsrInstr[_] = new UsrInstr(Bugif(), e)
  /** used very temporary to store the expression forming the body of a function*/
  //case class Result() extends Codop; def result(e: AST[_]): UsrInstr[_] = new UsrInstr(Result(), e)

  //private case class Affect(val name: String) extends Codop{override def toString=name+"\t<-"}; def affect(e: AST[_]): UsrInstr[_] = new UsrInstr(Affect(e.name), e)
}
