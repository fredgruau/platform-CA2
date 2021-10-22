package compiler

import compiler.AST._
import compiler.ASTB.Tminus1
import compiler.ASTBfun.{ASTBg, redop}
import compiler.InfoType._
import compiler.Instr._
import compiler.Locus.{deploy, _}
import compiler.VarKind._
import dataStruc.{Align, Dag, DagInstr, DagNode, SetInput, SetOutput}
import compiler.Circuit._
import dataStruc.Align.{compose, invert}

import scala.language.postfixOps
import scala.collection._
import scala.collection.immutable.HashSet

/** Instruction used within the compiler, call, affect. Dag and Union allows to defined ConnectedComp  */
abstract class Instr extends DagNode[Instr] with Align[Instr] with SetOutput[Instr] {
  def detm1ise(muName: String): Instr = if (names(0) != muName) this else new Affect(muName, exps(0).asInstanceOf[ASTBt[Ring]].detm1ise)


  /**
   *
   * @param x instruction input neighbor of  this
   * @return true if for example this.name is "shifttoto" and x's name is "toto"
   */
  def shiftandshifted(x: Instr) = isShift && (x.names(0) == unShifted)

  def unShifted = names(0).drop(5)

  def myZone(tZone: Map[String, Zone]) = tZone(root.names.head)

  def isFolded(tZ: Map[String, Zone]) = myZone(tZ).folded

  def inputFolded(tZ: Map[String, Zone]) = inputNeighbors.head.isFolded(tZ)

  def mySchedule(tZ: Map[String, Zone]): Array[Int] = {
    // if(names(0)=="distTslope")     printf("jysuis\njysuis\njysuis\njysuis\njysuis\njysuis\njysuis\njysuis\njysuis\n")
    val ps = myZone(tZ).pickedSchedule //schedule of root which is aux5 must be O51324
    val a = alignToRoot //alignement to root must be 240513 for distTslope

    val res = if (a != null) compose(ps, invert(a)) else null //must give 234501 will be null for shift instr
    res
  }

  /**
   * redefined in callProc
   *
   * @return
   */
  def callProcToAffect: Instr = this

  def tobeProcessedInMacro: Boolean = false

  def isReturn: Boolean = this match {
    case CallProc("return", _, _) => true;
    case _ => false
  }

  def exps: List[AST[_]]

  /**
   *
   * @param id1 rewriting of AST
   * @return instruction where rewriting has been applied on all expressions.
   */
  def propagate(id1: rewriteAST2): Instr

  override def aligned = !alignPerm.isEmpty //faut se mefier, ca va pas marcher pour load?


  /** true for instruction part or Transfer Connected Components */
  def isTransfer: Boolean

  /** @return the locus of expressions, for affectation. */
  def locus: Option[Locus] = None

  def ring: Option[Ring] = None

  def isV = locus.get == V()

  /** to be set if we want to use the Align feature, contains an alignment towards each usedvars of the instr (indexed by their name) */
  var alignPerm: iTabSymb[Array[Int]] = Map.empty

  /**
   * @return alignement from this to n.   */
  def neighborAlign(n: Instr): Array[Int] = {
    if (alignPerm.isEmpty)
      null
    else if (alignPerm.contains(n.names.head)) //n is a used var of this, so "this" is an element of n.neighbor,
      alignPerm(n.names.head) //neighborAligned(n.names(0))  is an alignement from "this" to n,
    else if (n.alignPerm.contains(names.head)) //ca doit etre le contraire, i.e. this is a used var of n. we find an alignement from n to "this", we must invert
      Align.invert(n.alignPerm(names.head))
    else throw new RuntimeException(" Not find alignement ")
  }

  // val exp:AST[T]
  /** @param hd head
   * @param tl  and tail  are built, in order to  find out the id of formal parameter passed by results. */
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
            if (t(r).k == MacroField()) t += r -> new InfoType(t(r).t, StoredField()); // register the fact that results must be stored.

          List(CallProc(c.f.namef, res, c.args.toList))
        case Taail(_) | Heead(_) => List() //we do not need those any more.
        case _ => List(this)
      }

      case _ => if (this.isReturn) List() else List(this)
    }
  }

  /**
   *
   * @param cur     The current programm
   * @param nbitLB  Stores number of bits of subfields.
   * @param tSymb   The symbol table with number of bits
   * @param newFuns Functions generated
   * @return The instructions rewritten so as to include Extend where necessary.
   */
  def bitIfy(cur: DataProg[InfoType[_]], nbitLB: AstField[Int], tSymb: TabSymb[InfoNbit[_]], newFuns: TabSymb[DataProg[InfoNbit[_]]]): Instr = this match {
    case Affect(s, exp) =>
      val newExp = exp.asInstanceOf[ASTLt[_, _]].bitIfy(cur, nbitLB, tSymb)
      tSymb += s -> new InfoNbit(cur.tSymbVar(s).t, cur.tSymbVar(s).k, nbitLB(newExp));
      Affect(s, newExp).asInstanceOf[Instr]
    case CallProc(f, names, exps) =>
      val newexps = exps.map(_.asInstanceOf[ASTLt[_, _]].bitIfy(cur, nbitLB, tSymb))
      val nbitarg = newexps.map(a => nbitLB(a)) //.toList.flatten
      val newnamef = f + nbitarg.map(_.toString).foldLeft("")(_ + "_" + _)

      //  if (f.size>2 && sysInstr.contains(f.substring(0,3)))
      if (isSysInstr(f))
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
  def unfoldSpace(m: Machine, tSymb: TabSymb[InfoNbit[_]]): List[Instr] =
    this match {
      case Affect(v, exp) => // println(exp.toStringTree) ;
        val exp2 = exp.asInstanceOf[ASTLt[_, _]]
        //processing redop separately


        exp2.locus match {
          case s: S => s.deploy(v).zip(exp2.unfoldSimplic(m)).map({ case (suf, e) => Affect(suf, e) }).toList

          //case s: S => s.sufx.zip(exp2.unfoldSimplic(m)).map({ case (suf, e) => Affect(v + "$" + suf, e) }).toList
          case l@T(s1, _) => s1.sufx.zip(exp2.unfoldTransfer(m)).map({
            case (suf1, t) =>
              l.sufx.zip(t).map({ case (suf2, e) => Affect(v + "$" + suf1 + suf2, e) }).toList
          }).toList.flatten
        }
      case CallProc(f, n, e) => List(CallProc(f, n.flatMap(Instr.deploy(_, tSymb)),
        e.asInstanceOf[List[ASTLt[_, _]]].flatMap(_.unfoldSpace(m)))) //tSymb(n).t._1
    }

  def locus2: Option[Ring] = None
}

/**
 * call of a procedure,
 * where several parameters can be passed by result.
 *
 * @param p     procedure's' name
 * @param names resutl's name
 * @param exps  passed as data
 */
case class CallProc(var p: String, names: List[String], exps: List[AST[_]]) extends Instr {
  override def callProcToAffect: Instr = if (tobeProcessedInMacro) new Affect(names(0), exps(0))
  else throw new Exception("only memo callProc gets macroified");


  override def tobeProcessedInMacro =
    isProcessedInMacro(p)

  // override def namesDefined: List[String] = if() List()
  /**
   * for bug and show we will add the name of the motherLayer to the name of the call
   *
   * @param motherLayer : Layer to which the bug or the show is attached
   */
  def preciseName(motherLayer: String) = p += motherLayer

  /**
   * @return string shows the results being affected simultaneously
   */
  override def toString: String = pad(names.mkString(","), 25) + "<-" + p + "(" + exps.map(_.toStringTree).mkString(" ") + ")\n"


  //override def toString: String = pad(names.foldLeft(" ")(_ + "," + _).substring(2), 25) + "<-" + p + "(" + exps.map(_.toStringTree).foldLeft(" ")(_ + " " + _) + ")\n"

  /**
   *
   * @return variables name used by the instruction
   */
  def usedVars(considerShift: Boolean = true): HashSet[String] = exps.map(_.symbolsExcepLayers).foldLeft(immutable.HashSet.empty[String])(_ | _)

  override def isTransfer: Boolean =
    throw new RuntimeException("test isTransfer is done only in macro, which do not have CallProc instr. ")

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
  override def usedVars(considerShift: Boolean = true): HashSet[String] = HashSet(shifted)

  override def names: List[String] = List(name)

  // override def namesDefined: List[String] = List(shifted)
}

//todo on aurait pas du prendre de case class pour affect ou callProc.
case class Affect[+T](name: String, val exp: AST[T]) extends Instr {

  def addParamR(tSymbVar: TabSymb[InfoNbit[_]]): List[Instr] = {
    if (tSymbVar(name).k == ParamR() && isRedop) {
      val newName = name + "R"
      tSymbVar.addOne(newName, tSymbVar(name))
      tSymbVar.addOne(name, tSymbVar(name).macroFieldise)
      val t = tSymbVar(name)
      val newAffect = Affect(newName, readLR(name, exp.mym.asInstanceOf[repr[(Locus, Ring)]]))
      List(this, newAffect)

    }
    else List(this)
  }

  /**
   *
   * @param dagZones
   * @param zones zones indexed by names
   * @return the zone to which the instruction belong
   */
  def myZone(dagZones: Dag[Zone], zones: iTabSymb2[Zone]) = zones(a(root).name)

  //def isReducedOfFolded= exp.isInstanceOf[RedO]
  def exps = List(exp)

  def isRedop = exp.asInstanceOf[ASTL.ASTLg]
    .isRedop

  val names = List(name);
  val namesDefined = List(name);

  override def toString: String = pad(name, 25) + "<-  " + exp.toStringTree + show(locus) + show2(locus2) +
    (if (alignPerm.isEmpty) "" else alignPerm.map({ case (k, v) => " aligned on: " + k + " with: " + v.toList + ";  " })) + "\n"

  private def show(x: Option[Locus]) = x match {
    case Some(s) => "" + s
    case None => ""
  }

  private def show2(x: Option[Ring]) = x match {
    case Some(s) => "" + s
    case None => ""
  }

  def usedVars(considerShift: Boolean = true): HashSet[String] = {
    if (isShift && considerShift) HashSet.empty
    else exp.symbolsExcepLayers
  }


  /** @return if instruction is ASTLt, returns the locus */
  override def locus: Option[Locus] = exp match {
    case a: ASTLt[_, _] => Some(a.locus)
    case _ => None
  }

  /** @return if instruction is ASTLt, returns the locus */
  override def ring: Option[Ring] = exp match {
    case a: ASTLt[_, _] => Some(a.ring)
    case _ => None
  }

  override def locus2: Option[Ring] = exp match {
    case a: ASTBt[_] => Some(a.ring)
    case _ => None
  }

  override def isTransfer: Boolean = exp.asInstanceOf[ASTLt[_, _]].locus.isInstanceOf[TT] // || exp.isInstanceOf[Red2[_,_,_]]
  override def propagate(id1: rewriteAST2): Instr = Affect(name, id1(exp))

  def coalesc(newName: iTabSymb[String]): Affect[_] =
    Affect(if (!newName.contains(name)) name else newName(name), exp.asInstanceOf[ASTBt[_]].coalesc(newName))

  /**
   *
   * @param cs conxtraints for cycle
   * @param t  updated with new symbols
   * @return aligned instruction, together with shift affect
   */
  def align(cs: TabSymb[Constraint], t: TabSymb[InfoNbit[_]]): List[Instr] = {
    val r = Result()
    val newExp = exp.asInstanceOf[ASTLt[_, _]].align(r, t)
    val newAffect = Affect(name, newExp)
    newAffect.alignPerm = r.algn
    var result: List[Instr] = List()
    if (r.c != None) {
      cs.addOne(name -> r.c.get)
      result = r.si.values.toList
    }
    newAffect :: result //We return  also the shift-affect instruction
  }
}

object Instr {
  val sysInstr = HashSet("ret", "bug", "sho", "mem")

  /**
   *
   * @return true for callProc that will not need to store their result in storedField, but instead are executed directly
   **/
  def isProcessedInMacro(p: String) = p == "memo" //TODO programmer memo comme une sous classe de callProc
  //|| p.startsWith("bug") we decide to keep call to bug outside macro
  // memo will be replaced by affectation to paramR, when moved to macro


  /**
   *
   * @param f name of a procedure
   * @return true if f is a system call
   */
  def isSysInstr(f: String) = f.size > 2 && sysInstr.contains(f.substring(0, 3))

  /** @param i instruction
   * @return i.asInstanceOf[Affect[_]]*/
  def a(i: Instr): Affect[_] = i.asInstanceOf[Affect[_]]

  def readLR(s: String, m: repr[(Locus, Ring)]) = new Read(s)(m) with ASTLt[Locus, Ring]

  def readR(s: String, m: repr[Ring]) = new Read(s)(m) with ASTBt[Ring]

  def tm1R(e: ASTBt[Ring], m: repr[Ring]) = new Tminus1(e)(m) with ASTBt[Ring]

  def reduceR(a1: ASTBg, a2: ASTBg, opred: redop[Ring], m: repr[Ring]) =
    new Call2(opred._1, a1, a2)(m) with ASTBt[Ring]


  /** utility used to align instruction when printed */
  def pad(s: String, n: Int): String = s + " " * (n - s.length())

  //  def apply(s: String, p: ProgData2): Instr = CallProc(s, p.paramR,
  //    p.paramD.map(x => read(x, repr(p.tSymbVar(x).t).asInstanceOf[repr[(_ <: Locus, _ <: Ring)]])))

  /**
   * @param s name of function
   * @param p the function itself
   * @return call to that function. effective parameter's name, are identical to formal.
   */
  def apply(s: String, p: DataProg[InfoNbit[_]]): Instr = {
    val call = CallProc(s, p.paramR, p.paramD.map(x => readLR(x, repr(p.tSymbVar(x).t).asInstanceOf[repr[(_ <: Locus, _ <: Ring)]])))
    call
  }

  /**
   *
   * @param n identifier
   * @param tSymb
   * @return add one (resp. two) suffixes to the variable names, for simplicial (resp. tranfer) variable
   */
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
      val newName = if (!already || already && tsymb(e.name).k == MacroField()) e.name else newFunName2()
      //we create another variable to return result, in case it is a layer.
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



