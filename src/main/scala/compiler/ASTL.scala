package compiler

import compiler.AST._
import compiler.ASTB._
import compiler.ASTBfun._
import compiler.ASTL._
import compiler.Align._
import compiler.Constraint._
import compiler.ProgData._
import compiler.repr._

import scala.collection._
import scala.reflect.ClassTag

/**The 9 locus. Three simplicial locus: V for vertex, E for edge, F for face, */
sealed abstract class Locus {
  /**suffix of variable names representing simplicial types */
  val sufx: Array[String]
  def isTransfer = false
  def arity: Int = if (isTransfer) 6 else sufx.length

  /**encodes a neutral permutation with the right number of elements. */
  lazy val neutral: Array[Int] = Array.range(0, arity) //we put lazy otherwise pb in initialization order
}
abstract class S extends Locus with Ordered[S] {
  def propagateFrom(s: Array[Int], c: Array[Int]): Option[Array[Int]]
  def compare(that: S): Int = { toString.compareTo(that.toString) }
  /** defines which components are regrouped upon partitionning a transfer variable */
  val proj: Array[Int]
  /** how to project a schedule */
  def scheduleProj(t:Seq[Int]):Array[Int]
  /**Number of schedule that can be partitionned */
  val card: Int

  /**Number of schedule that can be partitionned and verify a strict ordering */
  val cardSucc: Int
  val partitionnables: Option[Iterator[Array[Int]]]


}
final case class V() extends S {
  val sufx: Array[String] = Array("")
  val proj: Array[Int] = Array(0, 0, 0, 0, 0, 0); val card = 0; val cardSucc = 0
  def propagateFrom(s: Array[Int], c: Array[Int]): Option[Array[Int]] = None
  /** how to project a schedule, useless for V */
  override def scheduleProj(t: Seq[Int]): Array[Int] = Array(0)
  val partitionnables: Option[  Iterator[Array[Int]]] =  None

}

final case class E() extends S {
  /* "h" stands for horizontal, "d" diagonal, "ad" antidiagonal */
  val sufx: Array[String] = Array("h", "d", "ad");
  val proj: Array[Int] = Array(0, 0, 1, 1, 2, 2); val card = 48; val cardSucc = 6
  def propagateFrom(s: Array[Int], c: Array[Int]): Option[Array[Int]] = Some(Array(c(s(0) * 2), c(s(0) * 2) + 1, c(s(1) * 2), c(s(1) * 2) + 1, c(s(2) * 2), c(s(2) * 2) + 1))
  /** how to project a schedule */
  override def scheduleProj(t: Seq[Int]): Array[Int] = Array(proj(t(0)),proj(t(2)),proj(t(4)))
  private val modif=List(Array(0,0,0),Array(0,0,1),Array(0,1,0),Array(0,1,1),Array(1,0,0),Array(1,0,1),Array(1,1,0),Array(1,1,1) )
  private def combine(t:Array[Int],u:Array[Int]): Array[Int] =Array(t(0)+u(0),t(0)+1-(u(0)),t(1)+u(1),t(1)+1-(u(1)),t(2)+u(2),t(2)+1-u(2))
  val partitionnables: Option[Iterator[Array[Int]]] = Some(Array(0, 2, 4).permutations.flatMap((t: Array[Int]) => modif.map(combine(t, _))))

};

final case class F() extends S {
  val sufx: Array[String] = Array("up", "do"); val proj: Array[Int] = Array(0, 0, 0, 1, 1, 1); val card = 48; val cardSucc = 2
  def propagateFrom(s: Array[Int], c: Array[Int]): Option[Array[Int]] = Some(Array(c(s(0) * 3), c(s(0) * 3) + 1, c(s(0) * 3 + 2), c(s(1) * 3), c(s(1) * 3) + 1, c(s(1) * 3 + 2)))
  override def scheduleProj(t: Seq[Int]): Array[Int] = Array(proj(t(0)),proj(t(3)))
  private val  p2=List(3,4,5).permutations
  private def combine(t:List[Int],u:List[Int]): Seq[Array[ Int]] = List( (t:::u).toArray,(u:::t).toArray )
  val partitionnables: Option[Iterator[Array[Int]]] = Some( List(0, 1, 2).permutations.flatMap((t: List[Int]) => p2.map(combine(t, _))).flatten)

}

 abstract class TT extends Locus
/** T stands for Transfer, and uses two simplicial locus. The first is the simplicial. T[V,E] corresponds to  eV  */
final case class T[+S1 <: S, +S2 <: S](from: S1, to: S2) extends TT {
  override def isTransfer = true
  val sufx: Array[String] = from match {
    case V() => to match { case E() => Array("w", "nw", "ne", "e", "se", "sw") case F() => Array("wn", "n", "en", "es", "s", "ws") }
    case E() => to match { case V() | F() => Array("1", "2") }
    case F() => to match { case E() => Array("p", "b1", "b2") case V() => Array("b", "s1", "s2") } //"s" stands for side, "b" for base.
  }
}

/**
 * AST of spatial type
 *  @tparam L: the locus in V,E or F   *  @tparam R: the  type   *  @constructor
 *  @param m: implicit used to compute the locus and scala type
 *  made a lot of effort to make it covariant, but that seems useless, in fact.
 *  I've put the type locus + ring as part of  the case construct's fields, so that it becomes very easy to copy
 */
sealed abstract class ASTL[L <: Locus, R <: Ring]()(implicit m: repr[(L, R)]) extends ASTLt[L, R] {
  override def toString: String =
    this.asInstanceOf[ASTL[_, _]] match {
      //  case Layer(s, _)                 => "Layer " + this.name + ":" + locus.toString.charAt(0) + "-" + ring.toString.charAt(0)
      case _: Layer[_, _]              => "Layer " + this.name + ":" + locus.toString.charAt(0) + "-" + ring.toString.charAt(0)
      case Const(cte, _, _)            => "Const" + cte.toString + locus.toString.charAt(0) + "_" + ring.toString.substring(0, ring.toString.length() - 2);
      case Binop(op, _, _, _, _) => op.namef
      //  case Multop(op, args,_,_)      => op.toString
      case Unop(op, _, _, _)         => op.namef
      case Redop(op, _, _, _)        => "red" + op._1.namef
      case Clock(_, dir)       => if (dir) "clock" else "anticlock"
      case e @ Broadcast(_, _, _)    => "Broadcast" + ("" + (e.locus.asInstanceOf[T[_, _]] match { case T(_, y) => y })).charAt(0)
      case e @ Send(_)              => "Send" + ("" + (e.locus.asInstanceOf[T[_, _]] match { case T(_, y) => y })).charAt(0)
      case Transfer(_, _, _)         => "Transfer"
      case Sym(_, _, _, _)           => "sym "
    }

  /**No need to override, because signagure is distinct from AST's propagate */
  def propagate(id: bij[L, R]): ASTL[L, R] = {
    def id2[L3 <: Locus, R3 <: Ring]: bij[L3, R3] = d => id(d.asInstanceOf[ASTLt[L, R]]).asInstanceOf[ASTLt[L3, R3]] //introduit des variables libres
    val newD = this.asInstanceOf[ASTLg] match {
      case e: EmptyBag[_]            => e
      case e @ Broadcast(a, _, _)    => e.copy(arg = id2(a))
      case e @ Send(a)               => e.copy(args = a.map(id2))(lpart(e.mym), rpart(e.mym))
      case e @ Transfer(a, _, _)     => e.copy(arg = id2(a))
      case e @ Unop(_, a, _, _)     => e.copy(arg = id2(a))
      case e @ Binop(_, a, a2, _, _) => e.copy(arg = id2(a), arg2 = id2(a2))
      case e @ Redop(_, a, _, _)    => e.copy(arg = id2(a))
      case e @ Clock(a, _)     => e.copy(arg = id2(a))(lpart(e.mym), rpart(e.mym))
      case e @ Sym(a, _, _, _)       => e.copy(arg = id2(a))
    }; newD.setName(this.name); newD.asInstanceOf[ASTL[L, R]]
  }

  override def nbit(cur: ProgData1[_], nbitLB: AstField[Int], tSymb: TabSymb[InfoNbit[_]], newFuns: TabSymb[ProgData2]): ASTLt[L, R] = {
    val nbitB = immutable.HashMap.empty[AST[_], Int] //stores the bit number of an ASTB expression
    val nbitP = mutable.HashMap.empty[Param[_], Int] //virgin, to retrieve the nbits computed for the param.
    val result = this match {
      case Binop(op, a, a2, l2, r2) => //BINOP needs more work, because it triggers possible insertion of a new node "extend";
        var anew = a.nbit(cur, nbitLB, tSymb, newFuns); var a2new = a2.nbit(cur, nbitLB, tSymb, newFuns)
        //we start evaluation of binop by adding the number of bits of the arguments
        val startnbitB = nbitB + (op.p1 -> nbitLB(anew)) + (op.p2 -> nbitLB(a2new))
        val nbitResult = ASTB.nBitR(startnbitB, op.arg, nbitP) //retrieves the number of bit computed from the call to the ASTBfun.
        if (nbitP.contains(op.p1)) anew = anew.extendMe(nbitP(op.p1))
        if (nbitP.contains(op.p2)) a2new = a2new.extendMe(nbitP(op.p2))
        val newthis = Binop(op, anew, a2new, l2, r2)
        nbitLB += newthis -> nbitResult //the hashtable stores the number of bits of the newly computed tree.
        newthis
      case _ => //in all the other cases, no change is done on the AST, only  nbitLB is updated.
        val newthis = this.propagate((d: ASTLt[L, R]) => d.nbit(cur, nbitLB, tSymb, newFuns))

        def newNbit() = nbitLB(newthis.asInstanceOf[Singleton[AST[_]]].arg) //the nbit value of the arg is stored in nbitLB
        nbitLB += newthis -> (newthis.asInstanceOf[ASTL[_, _]] match {
          // case l:Layer[_,_] =>  l.nbit
          case Const(cte, _, _) => ASTB.nBitR(nbitB, cte, nbitP)
          case Unop(op, _, _, _) => ASTB.nBitR(nbitB + (op.p1 -> newNbit()), op.arg, nbitP)
          case Redop(_, _, _, _) | Clock(_, _) | Transfer(_, _, _) | Broadcast(_, _, _) | Sym(_, _, _, _) => newNbit()
          case Send(_) => nbitLB(newthis.asInstanceOf[Neton[AST[_]]].args.head)
          //FIXME for the concat redop, the number of bit must take into account the arity (2,3, or 6)
        })
        newthis
    }; result.setName(this.name); result
  }
  override def concatElt: Boolean = this match {
    case Unop(Fundef1("elt", _, _), arg, _, _) => arg.concatElt
    case Binop(Fundef2("concat", _, _, _), arg, arg2, _, _) => arg.concatElt && arg2.concatElt
    case _ => super.concatElt
  }

  override def unfoldSimplic(m: Machine): ArrAst = {
    val r = rpart(mym.asInstanceOf[repr[(L, R)]])
    val s = this.locus.asInstanceOf[S]
    this.asInstanceOf[ASTLg] match {
      case Const(cte, _, _)   => Array.fill(s.sufx.length)(cte)
      case Broadcast(_, _, _) => throw new RuntimeException("Broadcast creates   a transfer type")
      case Send(_)            => throw new RuntimeException("Broadcast creates   a transfer type")
      case Transfer(_, _, _)  => throw new RuntimeException("Transfer creates   a transfer type")
      case Unop(op, a, _, _)  => a.unfoldSimplic(m).map(new Call1(op.asInstanceOf[Fundef1[Any, R]], _)(r) with ASTBt[R])
      case Binop(op, a, a2, _, _) => a.unfoldSimplic(m).zip(a2.unfoldSimplic(m)).map({
        case (c, c2) => new Call2(op.asInstanceOf[Fundef2[Any, Any, R]], c, c2)(r) with ASTBt[R].asInstanceOf[ASTBg]
      })
      case Redop(op, a, _, _) =>
        def reduce(as: Array[ASTBt[R]], opred: redop[R]) = as.toList.tail.foldLeft(as(0))(new Call2(opred._1, _, _)(r) with ASTBt[R])
        a.unfoldTransfer(m).map((x: ArrAst) => reduce(x.asInstanceOf[Array[ASTBt[R]]], op.asInstanceOf[redop[R]])).asInstanceOf[ArrAst]
      case Clock(_, _) => throw new RuntimeException("Clock creates    a transfer type")

      case Sym(_, _, _, _)     => throw new RuntimeException("Sym creates  a transfer type")
    }
    //read and Call treated in ASTLt.

  }
  override def unfoldTransfer(m: Machine): ArrArrAst = {
    val T(s1, des) = this.locus; val l2 = this.locus.sufx.length
    this.asInstanceOf[ASTLg] match {
      case Const(cte, _, _)   => Array.fill(s1.sufx.length, l2)(cte)
      case Broadcast(a, _, _) => a.unfoldSimplic(m).map(Array.fill(l2)(_))
      case Send(a) =>
        if (a.length != l2) throw new RuntimeException("incorrect number of arguments for send")
        a.toArray.map(_.unfoldSimplic(m)).transpose
      case Transfer(a, _, _) => m(des, s1, a.unfoldTransfer(m))
      case Unop(op, a, _, n) => a.unfoldTransfer(m).map(_.map(new Call1(op.asInstanceOf[Fundef1[Any, R]], _)(n.asInstanceOf[repr[R]]) with ASTBt[R].asInstanceOf[ASTBg]))
      case Binop(op, a, a2, _, n) => a.unfoldTransfer(m).zip(a2.unfoldTransfer(m)).map({
        case (b, b2) => b.zip(b2).map({
          case (c, c2) =>
            new Call2(op.asInstanceOf[Fundef2[Any, Any, R]], c, c2)(n.asInstanceOf[repr[R]]) with ASTBt[R].asInstanceOf[ASTBg]
        })
      })
      case Redop(_, _, _, _) => throw new RuntimeException("Reduces create a simplicial type, not a transfer type")
      case Clock(a, dir) =>
        val T(_, src) = a.locus
        val trigo = !dir
        val atr = a.unfoldTransfer(m)
        if ((src < des) ^ dir) atr else atr.map(rot(_, trigo))
      case Sym(a, _, _, _) =>
        val T(s1, src) = a.locus; val atr = a.unfoldTransfer(m).map(rotR(_)); s1 match {
          case V() => atr.map(rotR(_)).map(rotR(_))//throw new RuntimeException("sym not defined on V in the general case")
          case E() => atr // la composée de deux rotation est une rotation simple qui est aussi une permutation pour E.
          case F() => if (src < des) atr else atr.map(rotR(_)) //we follow trigonometric, the composition of tree anticlock  must add one rotation, if not(src<des).
        }
      //read and Call treated in ASTLt.
    }
  }

  def shouldAffect: Boolean = this match {
    case Redop(_, _, _, _)      => true
     case Binop(_, a1, a2, _, _) => a1.isInstanceOf[ASTL.Clock[_, _, _, _]] || a2.isInstanceOf[ASTL.Clock[_, _, _, _]] || a1.isInstanceOf[ASTL.Sym[_, _, _, _]] || a2.isInstanceOf[ASTL.Sym[_, _, _, _]]//that's an overkill, unnecessary introduced variables will have to be removed
    case _                      => false
  }
  /** used to compute the expression being reduced.  */
  override def redExpr : List[AST[_]]= this match{
    case Redop(_, arg, _, _)      => List(arg)
    case _ => List()
  }

  override def align(cs: TabConstr, v: String): iTabSymb[Array[Int]] = {
    this.asInstanceOf[ASTLg] match { //read and Call treated in ASTLt.
      case Const(_, _, _)       => immutable.HashMap()
      case Broadcast(arg, _, _) => arg.align(cs, v).map { case (k, _) => k -> arg.locus.proj } //does not depend on v, because v is constant
      case Send(args)           => immutable.HashMap.empty ++ args.flatMap(a => a.align(cs, v).map
        { case (k, _) => k -> a.locus.proj }) //we can make  a union because does not depend on v
      case Transfer(arg, _, _) =>
        val T(s1, s2) = arg.locus; val t = hexPermut((s1, s2)); composeAll(t, arg.align(cs, v))
      case Unop(_, arg, _, _) => arg.align(cs, v)
      case Binop(_, arg, arg2, _, _) =>
        //be compute the constraint cycle here, because we can
        val a1 = arg.align(cs, v); val a2 = arg2.align(cs, v)
        val k = a1.keys.toSet.intersect(a2.keys.toSet)
        if (k.nonEmpty) { //k is the aux defined by an instr which will have to use two registers.
          val e = k.head //here we assume that there is a single input variable
          if (!(a1(e) sameElements a2(e)))
            cs += v ->  Cycle( compose(invert(a1(e)), a2(e)))
        }
        a1 ++ a2 //arg2 has priority over arg if non equal
      case Redop(_, arg, _, _) => //we compute a constraint, that is implicitely, the constraint to be checked for partitionning the Reduction. 
        
        arg.align(cs, v) //Redop is done in 6 instruction that will be scheduled according to the alignemet of its operand.
          //note that here, the expression has a simplicial type, thus, the alignement is not used to compute an alignement to a root,
          //it will be used to schedule the 6 redop operations. we will have to compose with the alignement to the root of the reduced transfer variable.
      
      
      case Clock(arg, dir) =>
        val T(_, des) = this.locus; val T(_, src) = arg.locus; val trigo = !dir; val atr = rotPerm(if (trigo) 1 else 5) //faudrait vérifier is c'est pas le contraire
        if ((src < des) ^ dir) arg.align(cs, v) else composeAll(atr, arg.align(cs, v))
      case Sym(arg, _, _, _) =>
        val T(_, des) = this.locus; val T(s1, src) = arg.locus; val atr = rotPerm(s1 match { case E() => 1 case F() => if (src < des) 1 else 2 case V() => 3 }); composeAll(atr, arg.align(cs, v))
      case l: Layer[_, _] => immutable.HashMap(l.name -> l.locus.neutral)
    }
  }
}
/**
 * At some point, we decided to store the type information for each distinct constructor, in order to have direct access to this info when copying the constructor,
 * this enabled to enforce the covariance in L:Locus and R:Ring, which was intuitive and would therefore facilitate things later on.
 * but then we abandonned it, so we could come back to previous setting where type was not stored, and copied in case class copying (see ASTBs).
 */
object ASTL {
  val u = 1
  private[ASTL] final case class Const[L <: Locus, R <: Ring](cte: ASTB[R], m: repr[L], n: repr[R]) extends ASTL[L, R]()(repr.nomLR(m, n)) with EmptyBag[AST[_]]
  private[ASTL] final case class Broadcast[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[S1, R], m: repr[T[S1, S2]], n: repr[R])
    extends ASTL[T[S1, S2], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]
  private[ASTL] final case class Send[S1 <: S, S2 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, S2]], n: repr[R])
    extends ASTL[T[S1, S2], R]() with Neton[AST[_]]
  private[ASTL] final case class Transfer[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R], m: repr[T[S2, S1]], n: repr[R])
    extends ASTL[T[S2, S1], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]
  private[ASTL] final case class Unop[L <: Locus, R1 <: Ring, R2 <: Ring](op: Fundef1[R1, R2], arg: ASTLt[L, R1], m: repr[L], n: repr[R2])
    extends ASTL[L, R2]()(repr.nomLR(m, n)) with Singleton[AST[_]]
  private[ASTL] final case class Binop[L <: Locus, R1 <: Ring, R2 <: Ring, R3 <: Ring](op: Fundef2[R1, R2, R3], arg: ASTLt[L, R1], arg2: ASTLt[L, R2], m: repr[L], n: repr[R3])
    extends ASTL[L, R3]()(repr.nomLR(m, n)) with Doubleton[AST[_]]
  private[ASTL] final case class Redop[S1 <: S, S2 <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R], m: repr[S1], n: repr[R])
    extends ASTL[S1, R]()(repr.nomLR(m, n)) with Singleton[AST[_]]
  private[ASTL] final case class Clock[S1 <: S, S2 <: S, S3 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R], dir: Boolean)(implicit  m: repr[T[S1, S3]], n: repr[R])
    extends ASTL[T[S1, S3], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]
  private[ASTL] final case class Sym[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R], m: repr[T[S1, S2new]], t: CentralSym[S2, S1, S2new], n: repr[R])
    extends ASTL[T[S1, S2new], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]
  /**Field which has a value both  at time t, and t+1 */
  trait Strate[L <: Locus, R <: Ring] { val pred: ASTLt[L, R]; val next: ASTLt[L, R] }
  /**Unlike other constructors,  Layer is not defined as a case class, otherwise equality between two layer of identical number of bits would allways hold */
  abstract class Layer[L <: Locus, R <: Ring](val nbit: Int)(implicit m: repr[L], n: repr[R]) extends ASTL[L, R]() with EmptyBag[AST[_]] with Strate[L, R] {
    val v = 1
    /** the value at t, which  is represented as  the layer itself.*/
    val pred: ASTL[L, R] = this

    /**needed to visite the next fields */
    override def other: List[AST[_]] = next :: super.other
    /** instructions also includes updating the layer by storing the next value.  */
    override def sysInstrs: List[UsrInstr[AST[_]]] = UsrInstr.memorize(next).asInstanceOf[UsrInstr[AST[_]]] :: super.sysInstrs
  }
  def rotL[T](a: Array[T])(implicit m: ClassTag[T]): Array[T] = a.drop(1) :+ a(0)
  def rotR[T](a: Array[T])(implicit m: ClassTag[T]): Array[T] = a(a.length - 1) +: a.take(a.length - 1)
  def rotR[T](a: Array[T],jump:Int)(implicit m: ClassTag[T]): Array[T] = Array.concat (  a.drop( jump), a.take( jump)  )
  def rot[T](a: Array[T], dir: Boolean)(implicit m: ClassTag[T]): Array[T] = if (dir) rotR(a) else rotL(a) //dir=True correspond to trigonometric order
  def rotPerm(dec: Int): Array[Int] = { val r = new Array[Int](6); for (i <- 0 to 5) r(i) = (i + dec) % 6; r }
  def composeAll(p: Array[Int], t: iTabSymb[Array[Int]]): Map[String, Array[Int]] = t.map { case (k, v) => k ->  compose(p, v) }
  import scala.language.implicitConversions
  /**Allows to consider false and true as occurence of ASTLs */
  implicit def fromBool[L <: Locus](d: Boolean)(implicit m: repr[L]): ASTLt[L, B] = Const(Boolof(d), m, repr.nomB)
  /**Allows to consider integers as occurence of ASTLs */
  implicit def fromInt[L <: Locus, R <: I](d: Int)(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = Const(Intof(d)(n), m, n)
  type ASTLg = ASTLt[_ <: Locus, _ <: Ring]
  type bij[L <: Locus, R <: Ring] = ASTLt[L, R] => ASTLt[L, R]

/*****************the wrapper*******************/
  def displayIn(l: Layer[_ <: Locus, _ <: Ring], f: ASTLg): Unit = l.render(f)
  def bugIfIn(l: Layer[_ <: Locus, _ <: Ring], f: ASTL[_ <: Locus, B]): Unit = l.bugif(f)

  def const[L <: Locus, R <: Ring](cte: ASTB[R])(implicit m: repr[L], n: repr[R]): Const[L, R] = Const(cte, m, n)

  def sym[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], t: CentralSym[S2, S1, S2new], n: repr[R]): Sym[S1, S2, S2new, R] = Sym(arg, m, t, n)

  def v[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, V]], n: repr[R]): Broadcast[S1, V, R] = Broadcast[S1, V, R](arg, m, n); // for broadcast, we want to specify only the direction where broadcasting takes place.
  def e[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, E]], m2: repr[T[E, S1]], n: repr[R]): Broadcast[S1, E, R] = Broadcast[S1, E, R](arg, m, n); // this is done using three function e,v,f.
  def f[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, F]], m2: repr[T[F, S1]], n: repr[R]): Broadcast[S1, F, R] = Broadcast[S1, F, R](arg, m, n)


  def clock[S1 <: S, S2 <: S, S2new <: S, R <: Ring]( arg: ASTLt[T[S1, S2], R]) (implicit m: repr[T[S1, S2new]], n: repr[R]): Clock[S1, S2, S2new, R] =Clock[S1, S2, S2new, R](arg, dir = true)
  def anticlock[S1 <: S, S2 <: S, S2new <: S, R <: Ring]( arg: ASTLt[T[S1, S2], R]) (implicit m: repr[T[S1, S2new]], n: repr[R]): Clock[S1, S2, S2new, R] =Clock[S1, S2, S2new, R](arg, dir = false)





  //Build a tranfser, just like v,e,f, however specify a diffent Simplicial field for each component.
  def sendv[S1 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, V]], n: repr[R]): Send[S1, V, R] = { assert(args.length == 6 / args.head.locus.arity); Send[S1, V, R](args); } //TODO check the length of args
  // def sende[S1 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, E]], n: repr[R]) = Send[S1, E, R](args) ;
  //  def sendf[S1 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, F]], n: repr[R]) = Send[S1, F, R](args) ;

  //def castB2R[L<:Locus,R<:I]( arg: AST[L,B] )(implicit m : repr[L])  = Unop[L,B,R] (castB2RN[R],arg );
  def transfer[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S2, S1]], n: repr[R]): Transfer[S1, S2, R] = Transfer(arg, m, n)

  //def unop[L <: Locus, Ri <: Ring, Ro <: Ring](f: Fundef1[Ri, Ro])(implicit m: repr[L], n: repr[Ro]) = (arg1: ASTLt[L, Ri]) => Unop[L, Ri, Ro](f, arg1, m, n)
  def sign[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): ASTLt[L, SI] = Unop[L, SI, SI](ASTBfun.sign, arg1, m, nomSI)
  def halve[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = Unop[L, R, R](halveB.asInstanceOf[Fundef1[R, R]], arg1, m, n)
  def orScanRight[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, R, R] = Unop[L, R, R](halveB.asInstanceOf[Fundef1[R, R]], arg1, m, n)
  def gt[L <: Locus](arg1: ASTLt[L, SI])(implicit m: repr[L]): Unop[L, SI, B] = Unop[L, SI, B](elt(-1).asInstanceOf[Fundef1[SI, B]], arg1, m, repr.nomB); //-1 will be taken modulo nbit.
  def notNull[L <: Locus, R <: I](arg1: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, R, B] = Unop[L, R, B](notNullB.asInstanceOf[Fundef1[R, B]], arg1, m, repr.nomB)

  /** Instead of casting boolean to integer,  we define a logical and taking an int and a  bool*/
  def andLB2R[L <: Locus, R <: I](arg1: ASTLt[L, B], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Binop[L, B, R, R] = Binop[L, B, R, R](andLBtoR.asInstanceOf[Fundef2[B, R, R]], arg1, arg2, m, n)

  def elem[L <: Locus, R <: I](i: Int, arg: ASTLt[L, R])(implicit m: repr[L], n: repr[B]): Unop[L, R, B] = Unop[L, R, B](elt(i).asInstanceOf[Fundef1[R, B]], arg, m, n)

  def concat2[L <: Locus, R1 <: Ring, R2 <: Ring](arg1: ASTLt[L, R1], arg2: ASTLt[L, R2])(implicit m: repr[L], n: repr[I]): ASTL[L, I] = Binop(concat2f.asInstanceOf[Fundef2[R1, R2, I]], arg1, arg2, m, n)

  def extend[L <: Locus, R <: Ring](i: Int, arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, R, R] = Unop[L, R, R](ASTBfun.extend(i).asInstanceOf[Fundef1[R, R]], arg, m, n)

  //def concat[L <: Locus, R <: I](arg1: Seq[ASTLtrait[L, R]])(implicit m: repr[L], n: repr[R]) = Multop2[L, R, R](concatN, arg1,m,n);
  // def orR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]) = Redop[S1, S2, R]((orI.asInstanceOf[Fundef2[R, R, R]], False[R]), arg, m, n);
  def orR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] = Redop[S1, S2, R](orRedop[R], arg, m, n)

  def andR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] = Redop[S1, S2, R](andRedop[R], arg, m, n)

  def xorR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] = Redop[S1, S2, R](xorRedop[R], arg, m, n)

  def redOp2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Binop[T[S1, S2new], R, R, R] =
    Binop[T[S1, S2new], R, R, R](op._1, Clock[S1, S2, S2new, R](arg, dir = true ), Clock[S1, S2, S2new, R](arg, dir = false ) ,m,n)

  def xorR2[S1 <: S, S2 <: S, S2new <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S1, S2new]], n: repr[R]): Binop[T[S1, S2new], R, R, R] =
    redOp2[S1, S2, S2new, R](xorRedop[R], arg)

  def subESI[S2 <: S](arg: ASTLt[T[E, S2], SI])(implicit m: repr[E]): ASTLt[E, SI] =
    Redop[E, S2, SI]((subSI, Intof[SI](0)), arg, m, repr.nomSI).asInstanceOf[ASTLt[E, SI]]

  /**minR has two implementations depending if the integers to be compared are signed or unsigned.*/
  def minR[S1 <: S, S2 <: S, R <: I](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): ASTLt[S1, R] =
    if (arg.ring == SI()) Redop[S1, S2, SI]((minSI, Intof[SI](0)), arg.asInstanceOf[ASTLt[T[S1, S2], SI]], m, repr.nomSI).asInstanceOf[ASTLt[S1, R]]
    else Redop[S1, S2, UI]((minUI, Intof[UI](0)), arg.asInstanceOf[ASTLt[T[S1, S2], UI]], m, repr.nomUI).asInstanceOf[ASTLt[S1, R]]

  /** Delayed uses a trick found on the net, to have a call by name, together with a case class necessary to make the match*/
  def delayedL[L <: Locus, R <: Ring](_arg: => ASTLt[L, R])(implicit m: repr[(L, R)]): ASTLt[L, R] = { lazy val delayed = _arg; new Delayed[(L, R)](() => delayed) with ASTLt[L, R] }
  def cond[L <: Locus, R <: I](b: ASTLt[L, B], arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] =
    andLB2R[L, R](b, arg1) | andLB2R(~b, arg2)
  /**
   * computes an int with a single non zero bit which is the highest rank for which operand's bit is one if operand is null, output O.
   * this is an example of boolean function with a reused value: orScanRight.
   */
  def mstb[L <: Locus, R <: I](arg1: ASTL[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = { val y: ASTL[L, R] = orScanRight[L, R](arg1); y ^ halve(y) }
  def or[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg1.ring match {
    case B() => Binop(orB, arg1.asInstanceOf[ASTLt[L, B]], arg2.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case _   => Binop(orI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2, m, n)
  }).asInstanceOf[ASTL[L, R]]

  def and[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg1.ring match {
    case B() => Binop(andB, arg1.asInstanceOf[ASTLt[L, B]], arg2.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case _   => Binop(andI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2, m, n)
  }).asInstanceOf[ASTL[L, R]]

  def xor[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg1.ring match {
    case B() => Binop(xorB, arg1.asInstanceOf[ASTLt[L, B]], arg2.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case _   => Binop(xorI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2, m, n)
  }).asInstanceOf[ASTL[L, R]]

  def neg[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg.ring match {
    case B() => Unop(negB, arg.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
    case _   => Unop(negI.asInstanceOf[Fundef1[R, R]], arg, m, n)
  }).asInstanceOf[ASTL[L, R]]
  def opp[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): Unop[L, SI, SI] = Unop[L, SI, SI](oppSI, arg.asInstanceOf[ASTLt[L, SI]], m, repr.nomSI)
  //{ ASTL.Unop(opp.asInstanceOf[Fundef1[R, SI]], this, m, repr.nomSI) }

  
  /** uses a fixed val addUISI, and let the compiler believe that this val has the appropriate expected  type R=UI or R=SI  */
  def add[L <: Locus, R <: Ring](arg1: ASTLt[L, R], arg2: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = Binop(addUISI.asInstanceOf[Fundef2[R, R, R]], arg1, arg2, m, n)

  type ASTLtG = ASTLt[_ <: Locus, _ <: Ring]
  type IntV = ASTLt[V, SI]; type IntE = ASTLt[E, SI]; type IntF = ASTLt[F, SI]
  type IntvE = ASTLt[T[E, V], SI]; type InteV = ASTLt[T[V, E], SI]
  type IntvF = ASTLt[T[F, V], SI]; type IntfV = ASTLt[T[V, F], SI]
  type IntfE = ASTLt[T[E, F], SI]; type InteF = ASTLt[T[F, E], SI]
  type UintV = ASTLt[V, UI]; type UintE = ASTLt[E, UI]; type UintF = ASTLt[F, UI]
  type UintvE = ASTLt[T[E, V], UI]; type UinteV = ASTLt[T[V, E], UI]
  type UintvF = ASTLt[T[F, V], UI]; type UintfV = ASTLt[T[V, F], UI]
  type UintfE = ASTLt[T[E, F], UI]; type UinteF = ASTLt[T[F, E], UI]
  type BoolV = ASTLt[V, B]; type BoolE = ASTLt[E, B]; type BoolF = ASTLt[F, B]
  type BooleV = ASTLt[T[V, E], B]; type BoolvE = ASTLt[T[E, V], B]
  type BoolvF = ASTLt[T[F, V], B]; type BoolfV = ASTLt[T[V, F], B]
  type BoolfE = ASTLt[T[E, F], B]; type BooleF = ASTLt[T[F, E], B]
  //  def neg2[L <: Locus, R <: Ring](arg: AST2[L, R])(implicit m: repr[L], n: repr[R]) = Unop[L, R, R](negN[R], arg);
  // implicit def fromAST2[L<:Locus,R<:Ring](x:AST2[L, R]):ASTL[L,R]=x.asInstanceOf[ASTL[L,R]
}

