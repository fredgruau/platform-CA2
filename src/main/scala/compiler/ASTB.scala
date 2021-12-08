package compiler

import compiler.AST.{Doubleton, _}
import compiler.ASTB.{ParOp, _}
import compiler.ASTBfun._
import compiler.ASTL.rewriteASTLt
import compiler.Circuit.{AstPred, TabSymb, iTabSymb2}

import scala.collection._
import scala.collection.immutable.{HashMap, HashSet}
import scala.language.implicitConversions


/**
 * node of Abstract Syntax Tree corresponding to an arithmetic field  boolean, integer (signed or unsigned)
 * We wish to be able to preserve covariance of R we couldnot because of progpageASTB.
 */
sealed abstract class ASTB[R <: Ring]()(implicit m: repr[R]) extends ASTBt[R] {

  /** Binary code, LSB at head */
  def toBinary2(n: Int, size: Int): List[ASTB[B]] =
    if (size == 0) List() else (if (n % 2 == 1) True() else False()) :: toBinary2(n / 2, size - 1)

  def extend(n: Int, l: List[ASTBt[B]], v: ASTBt[B]) = l ::: List.fill(n - l.length)(v).asInstanceOf[List[ASTBt[B]]]


  /** return the affbool that label subtrees neares to the root */
  override def affBoolify(): List[ASTBt[B]] = {
    this.asInstanceOf[ASTBg] match {
      case AffBool(n, exp) => List(this.asInstanceOf[ASTBt[B]])
      case _ => inputNeighbors.flatMap(_.asInstanceOf[ASTBt[_]].affBoolify()) //super.affBoolify??
    }
  }

  /**
   * simplifies the expression directly
   *
   * @param gen contains a table to read number of bits or reads
   * @param env contains a table of param's expression to also compute their number of bits
   * @return compiled ASTBt */
  override def codeGen(i: Int, gen: CodeGen, name: String, env: HashMap[String, ASTBt[B]]): ASTBt[B] = {
    var name2 = name
    val exp = this.asInstanceOf[ASTBg] match {
      case Neg(x) => addNeg(x.codeGen(i, gen, null, env))
      case Xor(x, y) => addXor(x.codeGen(i, gen, null, env), y.codeGen(i, gen, null, env))
      case Or(x, y) => addOr(x.codeGen(i, gen, null, env), y.codeGen(i, gen, null, env))
      case And(x, y) => addAnd(x.codeGen(i, gen, null, env), y.codeGen(i, gen, null, env))
      case Mapp1(op, x) =>
        var newEnv = env + (op.p1.nameP -> x(0).asInstanceOf[ASTBt[B]].codeGen(i, gen, null, env))
        //we must add the second argument if it is present, as xb.
        if (x.size > 1)
          newEnv = newEnv + (op.namef -> x(1).asInstanceOf[ASTBt[B]].codeGen(i, gen, null, env))
        op.arg.asInstanceOf[ASTBt[B]].codeGen(i, gen, null, newEnv)
      case Mapp2(x, y, op) => //il se peut quon rajute un affect et augmente la tsymb
        val newEnv = env + (op.p1.nameP -> x.asInstanceOf[ASTBt[B]].codeGen(i, gen, null, env)) +
          (op.p2.nameP -> y.asInstanceOf[ASTBt[B]].codeGen(i, gen, null, env))
        op.arg.asInstanceOf[ASTBt[B]].codeGen(i, gen, null, newEnv)
      case sc@Scan1(x, op: Fundef2R[B], v, _, initUsed) =>
        if (gen.firstIter(i) && initUsed)
          affBoolConst(sc.scanVar, v, gen)
        else {
          val firstArg =
            if (gen.firstIter(i)) v
            else gen.readWithConst(sc.scanVar)
          val iShifted = if (initUsed)
            i - gen.step
          else i //takes into account the fact that scan's values are shifted
          val newEnv = env +
            (op.p1.nameP -> firstArg) +
            (op.p2.nameP -> x.asInstanceOf[ASTBt[B]].codeGen(iShifted, gen, null, env))
          val e = op.arg.asInstanceOf[ASTBt[B]].codeGen(i, gen, null, newEnv)
          if (gen.lastIter(i)) e
          else affBoolConst(sc.scanVar, e, gen)
        }
      case sc@Scan2(x, y, op: Fundef3R[B], v, _, initUsed) =>
        if (gen.firstIter(i) && initUsed)
          affBoolConst(sc.scanVar, v, gen)
        else {
          val firstArg =
            if (gen.firstIter(i)) v
            else gen.readWithConst(sc.scanVar) //sc10 first value vaut zero
          val iShifted = if (initUsed) i - gen.step else i //takes into account the fact that scan's values are shifted
          val newEnv = env +
            (op.p1.nameP -> firstArg) +
            (op.p2.nameP -> x.asInstanceOf[ASTBt[B]].codeGen(iShifted, gen, null, env)) +
            (op.p3.nameP -> y.asInstanceOf[ASTBt[B]].codeGen(iShifted, gen, null, env))
          val e = op.arg.asInstanceOf[ASTBt[B]].codeGen(i, gen, null, newEnv)
          if (gen.lastIter(i)) e
          else affBoolConst(sc.scanVar, e, gen)
        }
      case Shift(e, b) => Shift(e.codeGen(i, gen, null, env), b)
      case Tminus1(e) => Tminus1(e.codeGen(i, gen, null, env))
      case Elt(n, exp) =>
        val newExp = exp.asInstanceOf[ASTBt[B]].codeGen(i, gen, null, env)
        val indexElt = if (n == -1) gen.bitSize - 1 else n
        if (i == indexElt) AffBool(name, newExp) else if (i != indexElt)
          name2 = null
        newExp
      case Reduce(exp, op, init) =>
        val newExp = exp.asInstanceOf[ASTBt[B]].codeGen(i, gen, null, env)
        name2 = name //we allways make an affectation
        val newRedExp =
          if (gen.firstIter(i)) newExp
          else {
            val newEnv = env +
              (op.p1.nameP -> new Read(name)(repr(B)) with ASTBt[B]) +
              (op.p2.nameP -> newExp)
            op.arg.asInstanceOf[ASTBt[B]].codeGen(i, gen, null, newEnv)
          }
        newRedExp
      case ex@Extend(n: Int, exp: ASTBg) =>
        val nbitExp = exp.nBit(gen, env)
        var newExp: ASTBt[B] = null
        if (i < nbitExp) newExp = exp.asInstanceOf[ASTBt[B]].codeGen(i, gen, null, env)
        if (exp.mym.name == SI() && i == nbitExp - 1) affBoolConst(ex.scanVar, newExp, gen) //we store the sign bit
        else if (i < nbitExp) newExp
        else if (exp.mym.name == UI()) ASTB.False()
        else if (exp.mym.name == SI()) gen.readWithConst(ex.scanVar) // sign bit replicates
        else throw new Exception("extend bordel probably is UISI and we 'd need to know wether it is SI or UI")
      case exp@Intof(value: Int) =>
        val t = exp.mym.name.asInstanceOf[I];
        val nbit = nbitCte(value, t) //depends on wether t is signed or unsigned
        val p = scala.math.pow(2, nbit).toInt;
        fromBoolB(toBinary(value + (if (value >= 0) 0 else p), nbit)(i))
      case co@Concat2(exp1, exp2) =>
        val nbitExp1 = exp1.nBit(gen, env)
        //val nbitExp2=exp2.nBit(gen,env)
        if (i < nbitExp1)
          exp1.asInstanceOf[ASTBt[B]].codeGen(i, gen, null, env)
        else
          exp2.asInstanceOf[ASTBt[B]].codeGen(i - nbitExp1, gen, null, env)

    }
    affBoolConst(name2, exp.asInstanceOf[ASTBt[B]], gen)
  }

  override def deCallify(env: HashMap[String, ASTBg], ts: TabSymb[InfoNbit[_]]): ASTBg = {
    val rewrite: rewriteASTBt[R] = (d: ASTBt[R]) => d.deCallify(env, ts).asInstanceOf[ASTBt[R]]
    propagateASTB(rewrite)
  }


  override def toString: String =
    this.asInstanceOf[ASTB[_]] match {
      case AffBool(nameb, _) => nameb + ":="
      case Intof(v) => "" + v
      case True() => "truue"
      case False() => "faalse"
      case Concat2(x, y) => "::"
      case Elt(i, x) => "Elt" + i
      case Extend(i, _) => "Extend" + i //+ mym.name
      case Xor(x, y) => "^"
      case Or(x, y) => "|"
      case And(x, y) => "&"
      case Neg(x) => "!"
      case Mapp1(op, x) => "Mapp1" + op.namef //+ mym.name
      case Mapp2(x, y, op) => "Mapp2" + op.namef //+ mym.name
      case Scan1(x, op, _, dir, _) => "Scan1" + op.namef + dir //+ mym.name
      case Scan2(x, y, op, _, dir, _) => "Scan2" + op.namef + dir //+ mym.name
      case Reduce(x, op, _) => "Red" + op.namef
      case Shift(x, right) => (if (right) ">>" else "<<")
      case Tminus1(x) => "tm1"
    }

  /**
   * @param id rewriting procedure
   * @return ASTB obtained by applying the rewriting recursively
   *         No  override, because name is distinct from AST's propagate */
  def propagateASTB(id: rewriteASTBt[R]): ASTBt[R] = {
    def id2[R3 <: Ring]: rewriteASTBt[R3] = d => id(d.asInstanceOf[ASTBt[R]]).asInstanceOf[ASTBt[R3]] //introduit des variables libres
    val newD = this.asInstanceOf[ASTBg] match {
      case e: EmptyBag[_] => e
      case e@Xor(a, b) => e.copy(arg = id2(a), arg2 = id2(b))(e.mym)
      case e@Or(a, b) => e.copy(arg = id2(a), arg2 = id2(b))(e.mym)
      case e@And(a, b) => e.copy(arg = id2(a), arg2 = id2(b))(e.mym)
      case e@Neg(a) => e.copy(arg = id2(a))(e.mym)
      case e@Concat2(a, b) => val newe = e.copy(arg = id2(a), arg2 = id2(b))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Elt(_, a) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Extend(_, a) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Mapp1(_, a) => val newe = e.copy(args = a.map(id2(_)))(e.mym);
        newe.dirNarrowed = e.dirNarrowed;
        newe
      case e@Mapp2(a, b, _) => val newe = e.copy(arg = id2(a), arg2 = id2(b))(e.mym);
        newe.dirNarrowed = e.dirNarrowed;
        ;
        newe
      case e@Scan1(a, _, _, _, _) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Scan2(a, b, _, _, _, _) => val newe = e.copy(arg = id2(a), arg2 = id2(b))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Reduce(a, _, _) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Tminus1(a) => e.copy(arg = id2(a))(e.mym)
      case e@Shift(a, _) => e.copy(arg = id2(a))(e.mym)
    };
    newD.setName(this.name);
    newD.asInstanceOf[ASTB[R]]
  }


  override def detm1iseR: ASTBt[R] = {
    def id2[R3 <: Ring]: rewriteASTBt[R3] = d => d.asInstanceOf[ASTBt[R]].detm1iseR.asInstanceOf[ASTBt[R3]] //introduit des variables libres
    val newD = this.asInstanceOf[ASTBg] match {
      case e: EmptyBag[_] => e
      case e@Xor(a, b) => e.copy(arg = id2(a), arg2 = id2(b))(e.mym)
      case e@Or(a, b) => e.copy(arg = id2(a), arg2 = id2(b))(e.mym)
      case e@And(a, b) => e.copy(arg = id2(a), arg2 = id2(b))(e.mym)
      case e@Neg(a) => e.copy(arg = id2(a))(e.mym)
      case e@Concat2(a, b) => val newe = e.copy(arg = id2(a), arg2 = id2(b))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Elt(_, a) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Extend(_, a) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Mapp1(_, a) => val newe = e.copy(args = a.map(id2(_)))(e.mym);
        newe.dirNarrowed = e.dirNarrowed;
        newe
      case e@Mapp2(a, b, _) => val newe = e.copy(arg = id2(a), arg2 = id2(b))(e.mym);
        newe.dirNarrowed = e.dirNarrowed;
        ;
        newe
      case e@Scan1(a, _, _, _, _) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Scan2(a, b, _, _, _, _) => val newe = e.copy(arg = id2(a), arg2 = id2(b))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Reduce(a, _, _) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Tminus1(a) => id2(a)
      case e@Shift(a, _) => e.copy(arg = id2(a))(e.mym)
    };
    newD.setName(this.name);
    newD.asInstanceOf[ASTBt[R]]
  }

  /** remove the head tm1 */
  override def detm1ise: ASTBt[R] = this match {
    case ASTB.Tminus1(e) =>
      e.name = name; //propagates the name's change
      e
    case _ => this
  }

  override def isTm1 =
    this match {
      case Tminus1(_) => true
      case _ => false
    }

  override def isNotTm1Read =
    this match {
      case Tminus1(x) => isNotRead(x)
      case _ => true
    }

  /** we will not generate an affect for such expression, it cost only the negation operator, we prefer to recompute it */


}

/** static object using arithmetic parse trees, operators gets a name, using another method, with the letter 'n' appended
 * Important CODE CONVENTION: LSB first means that Least significant bit is head of list.
 **/
object ASTB {
  var totalScan = 0
  type rewriteASTBt[R <: Ring] = ASTBt[R] => ASTBt[R]

  /** Direction the pipelining process of integers's bit
   * left means from the least significant bits towards the msb, and   right is the other way round. */
  abstract sealed class Dir {
    def narrowed: Dir;

    def opposite: Dir
  }

  final case class Left() extends Dir {
    val narrowed = this;

    def opposite = Right()
  }

  final case class Right() extends Dir {
    val narrowed = this;

    def opposite = Left()
  }

  final case class Both() extends Dir {
    val narrowed = Left();

    def opposite = throw new Exception("Both has no opposite")
  }

  /*
    sealed class ParamUse
    final case class SingleUse() extends ParamUse
    final case class ToBeStored() extends ParamUse
    class Pipelined extends ParamUse
    case class PipelinedFirstUse() extends Pipelined
    case class PipelinedOthertUse() extends Pipelined
  */


  /** Communication Constructors, work for both Booleans and integers  */
  case class Shift[R <: Ring](arg: ASTBt[R], right: Boolean)(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton[AST[_]]

  /** All the constructors should be declared private for clean separtion. TMInus1 illustrates how to proceeds in this direction */
  private[ASTB] case class Tminus1[R <: Ring](arg: ASTBt[R])(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton[AST[_]]


  /** Bolean Constructor */
  class Bool extends ASTB[B] with EmptyBag[AST[_]]

  final case class True()(implicit n: repr[B]) extends ASTB[B] with EmptyBag[AST[_]] {
    override def isConst = true
  }

  final case class False()(implicit n: repr[B]) extends ASTB[B] with EmptyBag[AST[_]] {
    override def isConst = true
  }

  implicit def toBoolB(d: ASTBt[B]): Boolean = if (d == True()) true else if (d == False()) false else
    throw new Exception("pas boolean")

  def fromBoolB(d: Boolean): ASTBt[B] = if (d == true) True() else False()

  final case class Xor(arg: ASTBt[B], arg2: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Doubleton[AST[_]] //{assert(y.nbit==x.nbit)}
  final case class And(arg: ASTBt[B], arg2: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Doubleton[AST[_]] //{assert(y.nbit==x.nbit)}
  final case class Or(arg: ASTBt[B], arg2: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Doubleton[AST[_]] //{assert(y.nbit==x.nbit)}
  final case class Neg(arg: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Singleton[AST[_]]

  /** ¯Boolean Affectation are also expression */
  final case class AffBool(nameb: String, arg: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Singleton[AST[_]]

  def affBool(nameb: String, arg: ASTBt[B]) = if (nameb == null) arg else AffBool(nameb, arg)

  def affBoolConst(nameb: String, arg: ASTBt[B], g: CodeGen) =
    if (arg.isConst) {
      if (nameb != null) g.constant = g.constant + (nameb -> fromBoolB(arg));
      arg
    } //we need to return the constant because it could be afected to other variable
    else {
      if ((nameb != null) && (g.constant.contains(nameb))) g.constant = g.constant - nameb //variable are reused they can loose their status of bieng constant
      if (nameb == null) arg else AffBool(nameb, arg)
    }

  /** @param dir is a direction. that can be narrowed from both to left or right
   *             ParOp allows to easily computes direction and direction's narrowing if any. */
  abstract class ParOp[R <: Ring](val dir: Dir)(implicit n: repr[R]) extends ASTB[R] {
    /** if dir equals both but a child is rightWard, then we must be obliged to iterate rightward, we register this change in dirNarrowed */
    var dirNarrowed: Dir = dir
  }

  abstract class ParOpScan[R <: Ring](override val dir: Dir)(implicit n: repr[R]) extends ParOp[R](dir) {
    val nb = totalScan;
    totalScan += 1

    def scanVar = "_sc" + nb //fixme j'ai peur que si on apelle deux fois une fonction avec un scan on instancie deux fois le meme scanVar alors que il en faudrait deux distinctes
  }

  /** returns bit at position i, modulo nbit. Obs: -1 is the index of the last bit. */
  case class Elt[R <: I](i: Int, arg: ASTBt[R])(implicit n: repr[B]) extends ParOp[B](Both()) with Singleton[AST[_]]

  case class Reduce[R <: I](arg: ASTBt[R], op: Fundef2R[B], init: ASTBt[B])(implicit n: repr[B]) extends ParOp[B](Both()) with Singleton[AST[_]]


  val eltRed: AST[_] => Boolean = (x: AST[_]) => x.isInstanceOf[Reduce[_]] || x.isInstanceOf[Elt[_]]


  /** Integer Constructor */
  case class Intof[R <: I](value: Int)(implicit n: repr[R]) extends ParOp[R](Both()) with EmptyBag[AST[_]]

  case class Concat2[R1 <: Ring, R2 <: Ring, O1 <: I](arg: ASTBt[R1], arg2: ASTBt[R2])(implicit n: repr[O1])
    extends ParOp[O1](Both()) with Doubleton[AST[_]]

  /** in order to use a single concat to regroup arbitrary many components */
  case class ConcatN[R1 <: Ring, O1 <: I](args: List[ASTBt[R1]])(implicit n: repr[O1])
    extends ParOp[O1](Both()) with Neton[AST[_]]

  /** will copy the msb until nbits are obtained, we inherit parOpScan in order to enjoy a register to store that last bit */
  case class Extend[R <: Ring](i: Int, arg: ASTBt[R])(implicit n: repr[R]) extends ParOpScan[R](Left()) with Singleton[AST[_]]

  /** Iterates on one int */
  case class Mapp1Old[R <: I](arg: ASTBt[R], op: Fundef1[B, B])(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton[AST[_]]

  /** Iterates on one int */
  case class Mapp1[R <: I](op: Fundef1[B, B], args: List[ASTBt[R]])(implicit n: repr[R]) extends ParOp[R](Both()) with Neton[AST[_]]

  /** iterates on two ints with identical number of bits */
  case class Mapp2[R <: I](arg: ASTBt[R], arg2: ASTBt[R], op: Fundef2[B, B, B])(implicit n: repr[R])
    extends ParOp[R](Both()) with Doubleton[AST[_]] {
    assert(arg.mym.name == arg2.mym.name, "map2's operand must be both ui or both si")
  }

  /** iterate on one int, uses a carry */
  case class Scan1[R <: I](arg: ASTBt[R], op: Fundef2R[B], init: ASTBt[B], override val dir: Dir, initUsed: Boolean)(implicit n: repr[R])
    extends ParOpScan[R](dir) with Singleton[AST[_]]

  /** iterate on two ints with identical  number of bits, uses a carry */
  case class Scan2[R <: I](arg: ASTBt[R], arg2: ASTBt[R], op: Fundef3R[B], init: ASTBt[B], override val dir: Dir, initUsed: Boolean)
                          (implicit n: repr[R]) extends ParOpScan[R](dir) with Doubleton[AST[_]]

  /** *****Wrapping *********/
  def tm1(e: ASTBt[Ring])(implicit m: repr[Ring]) = new Tminus1(e)(m) with ASTBt[Ring]

  def shiftL[R <: Ring](arg: ASTBt[R])(implicit n: repr[R]): Shift[R] = Shift(arg, right = false)

  def shiftR[R <: Ring](arg: ASTBt[R])(implicit n: repr[R]): Shift[R] = Shift(arg, right = true)


  val lnOf2: Double = scala.math.log(2) // natural log of 2
  val Epsilon = 0.00001 //we add epsilon so that an exact power of two needs one bit more.
  def log2(x: Double): Int = scala.math.ceil(scala.math.log(x) / lnOf2).toInt

  /**
   *
   * @param n
   * @param t
   * @return return the minmimum number of bits needed to encode the signed integer n
   */
  def nbitCte(n: Int, t: I): Int = if (n < 0) {
    if (t != SI()) throw new RuntimeException("should be signed integer");
    1 + log2(-n - Epsilon)
  }
  else if (n == 0) 1 //the integer O takes one bit to store
  else log2(n + Epsilon) + (if (t == SI()) 1 else 0)

  /**
   * //TODO memoiser pour ne pas avoir a rappeler 40,000 fois add
   *
   * @param nbit stores the number of bits of parameters
   * @param d    the AST we want to know how many bits it has
   * @param pm   memorizes change of parameter 's bit number if any
   * @return bit size of $d
   */
  def nBitR(nbit: immutable.HashMap[AST[_], Int], d: AST[_], pm: mutable.HashMap[Param[_], Int], g: CodeGen): Int = {
    /** register parames that needs to be extended, with more bits, because they are combined with Ints having more bits.  */
    def levelup(x: AST[_], a1: Int, a2: Int): Unit = {
      if (a1 < a2) {
        x match {
          case p: Param[_] => pm += (p -> a2);
          case _ => throw new RuntimeException("pb bit number in ASTB")
        }
      }
    } //if not a parameter ca bugge.
    def maxim(x: AST[_], y: AST[_]): Int = {
      val (nx, ny) = (nBitR(nbit, x, pm, g), nBitR(nbit, y, pm,g))
      levelup(x, nx, ny);
      levelup(y, ny, nx);
      math.max(nx, ny)
    }

    d match {
      case Intof(n) => nbitCte(n, d.mym.name.asInstanceOf[I])

      //case BoolOf(_) => 1
      case True() | False() => 1
      case Call1(f, e) => nBitR(nbit + (f.p1 -> nBitR(nbit, e, pm, g)), f.arg, pm, g)
      case Call2(f, e, e2) => nBitR(nbit + (f.p1 -> nBitR(nbit, e, pm, g)) + (f.p2 -> nBitR(nbit, e2, pm, g)), f.arg, pm, g)
      case e@Param(_) => nbit(e)
      case Neg(x) => nBitR(nbit, x, pm, g)
      case Xor(_, _) => 1
      case Or(_, _) => 1
      case And(_, _) => 1
      case Scan1(exp, _, _, _, initused) => nBitR(nbit, exp, pm, g) + (if (initused) 0 else 0)
      case Scan2(exp, exp2, _, _, _, _) => maxim(exp, exp2)
      case Reduce(_, _, _) => 1 //FIXME doesnot work for the reduction with concat
      case Mapp2(exp, exp2, _) => maxim(exp, exp2)
      case Shift(e, _) => nBitR(nbit, e, pm, g)
      case Tminus1(e) => nBitR(nbit, e, pm, g)
      case Mapp1(_, expList) => nBitR(nbit, expList.head, pm, g)
      //case MappBI(exp, exp2, opp)               => nBitR(nbit, exp2, pm)
      case Elt(_, _) => 1;
      case Concat2(exp, exp2) => nBitR(nbit, exp2, pm, g) + nBitR(nbit, exp, pm, g) //
      case Extend(n, _) => n
      case Read(x) =>
        if (dataStruc.Named.isTmp(x) && g.tableAllAffect.contains(x))
          nBitR(nbit, g.tableAllAffect(x).exps(0), pm, g)
        else if (g.tableAllPipelined.contains(x))
          nBitR(nbit, g.tableAllPipelined(x).exps(0), pm, g)
        else if (g.tSymbVar.contains(x))
          g.tSymbVar(x).nb
        else if (g.coalesc.contains(x) && g.tSymbVar.contains(g.coalesc(x)))
          g.tSymbVar(g.coalesc(x)).nb
        else throw new Exception("where is " + x)
    }
  }

  def dir2(t: Any) = t.asInstanceOf[Affect[_]].exp.asInstanceOf[ASTBg].dir1

  /** Binary code, LSB at head */
  def toBinary(n: Int, size: Int): List[Boolean] =
    if (size == 0) List() else (if (n % 2 == 1) true else false) :: toBinary(n / 2, size - 1)

  /** Computes the names affected in the expression */
  def tmpNames(code1loop: List[ASTBt[B]]): (HashSet[String], HashSet[String]) = {
    def isTmp(s: String) = s != null && s.startsWith("_") && !s.startsWith("_aux")

    var resRead = HashSet[String]()
    var resDef = HashSet[String]()

    def tmpNames(exp: ASTBt[B]): Unit = {
      exp match {
        case AffBool(n, arg) =>
          if (isTmp(n)) resDef += n
        case r: Read[ASTBt[B]] =>
          if (isTmp(r.which)) resRead += r.which


        case _ =>
      }
      exp.inputNeighbors.map((t: AST[_]) => tmpNames(t.asInstanceOf[ASTBt[B]]))
    }

    for (bInst <- code1loop)
      tmpNames(bInst)
    (resDef, resRead)
  }


  def isNotMap1Read(iT: collection.Set[AST[_]]): AstPred = {
    case Mapp1(_, x :: _) =>
      AST.isNotRead(x) && (!iT.contains(x))
    case _ =>
      true
  }


  def addNeg(x: ASTBt[B]) = x match {
    case ASTB.False() => ASTB.True()
    case ASTB.True() => ASTB.False()
    case Neg(exp2) => exp2
    case newx@_ => Neg(newx)
  }

  def addXor(x: ASTBt[B], y: ASTBt[B]) = (x, y) match {
    case (False(), _) => y
    case (True(), _) => addNeg(y) // Neg may be further simplified
    case (_, False()) => x
    case (_, True()) => addNeg(x) // Neg may be further simplified
    case _ => Xor(x, y)
  }

  def addAnd(x: ASTBt[B], y: ASTBt[B]) = (x, y) match {
    case (False(), _) | (_, False()) => False()
    case (True(), _) => y
    case (_, True()) => x
    case _ => And(x, y)
  }

  def addOr(x: ASTBt[B], y: ASTBt[B]) = (x, y) match {
    case (False(), _) => y
    case (_, False()) => x
    case (True(), _) | (_, True()) => True() //we  could further simplify the Neg
    case _ => Or(x, y)
  }

}

