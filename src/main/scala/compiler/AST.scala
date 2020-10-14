package compiler
//toto
import compiler.AST._
import compiler.ProgData._

import scala.collection._
import scala.collection.immutable.HashSet

/**
 * Represent a field using an Abstract Syntax Tree using Function definition, and calls, reading of variables, delaying of evaluation.
 * Reused to implement  1- the AST of spatial  field (ASTL) and 2- the AST of arithmetic field(ASTB)
 * The parameter type T is the type of the associated expression
 * covariant because
 * @param m parameter used to compute this type. */
abstract class AST[+T]()(implicit m: repr[T]) extends Dag[AST[_]] with Named {
  val mym: repr[T] = m //if type of mym is set to repr[_] this allow covariance even if repr is not covariant
  /**  system instruction can be associated to any spatial field, so as to be latter retrievable from the compiling method. */
  private var sysInstr: List[UsrInstr[AST[_]]] = List.empty; def sysInstrs: List[UsrInstr[AST[_]]] = sysInstr
  override def other: List[AST[_]] = sysInstr.map(_.exp) //so that compute nodes used in instructions can be directly explored.
  /**@param a is true where there is a bug associated to the field "this" */
  def bugif(a: ASTLt[_ <: Locus, B]): Unit = { sysInstr ::= UsrInstr.bugif(a).asInstanceOf[UsrInstr[AST[_]]] }
  /** @param a allows to visualize "this" with a minimalistic coloring load on the screen*/
  def render(a: ASTL.ASTLg) { sysInstr ::= UsrInstr.display(a).asInstanceOf[UsrInstr[AST[_]]] }

  def checkName(): AST[T] = { if (name == null) name = "_aux" + AST.getCompteur; this }
  /** Builds the set of affected symbols which are read. */
  def reads: immutable.HashSet[String] = this match {
    case Read(s) => HashSet(s)
    case _       => inputNeighbors.map(e => e.reads).foldLeft(HashSet.empty[String])((x, y) => x.union(y))
  }
  /** Builds the set of symbols which are read . */
  def symbols: immutable.HashSet[String] = this match {
    case Read(s)             => HashSet(s)
    case Param(s)            => HashSet(s)
    case l: ASTL.Layer[_, _] => HashSet(l.name)
    case _                   => inputNeighbors.map(e => e.symbols).foldLeft(HashSet.empty[String])((x, y) => x.union(y))
  }

  override def toString: String = this.asInstanceOf[AST[_]] match {
    case Read(s)     => s
    case Param(s)    => "Param " + s
    // case f: Fundef[_]      => "Fundef " + f.namef + " of param " + f.p.map(p => p.nameP).foldLeft("")(_ + ", " + _)
    case c: Call[_]  => c.f.namef + " "
    case Heead(_)    => "head"
    case Taail(_)    => "tail"
    case Coons(_, _) => "cons"
    case _           => throw new RuntimeException("merdouille")
  }

  /**
   * Important to specify that the L,R type of AST nodes is preserved, for type checking consistency
   * Surprisingly, when building ASTL explicitely, we need to drop the fact that the type is preserved, and go from ASTL[L,R] to ASTLg
   * Transform a Dag of AST into a forest of trees, removes the delayed.
   * @param usedTwice  dags which are used twice, or which need to be affected for some other reason.
   * @param repr: representant of the equivalence class with respect to equal on case class hierarchy
   * @param replaced: map encoding a substitution.
   * @return the Dag where expression used more than once are replaced by read.
   */
  def deDag(usedTwice: immutable.HashSet[AST[_]], repr: Map[AST[_], AST[_]], replaced: Map[AST[_], AST[_]]): AST[T] = {
    if (usedTwice.contains(this)) new Read[T](repr(this).name)(mym.asInstanceOf[repr[T]])
    else if (replaced.contains(this)) replaced(this).asInstanceOf[AST[T]].deDag(usedTwice, repr, replaced)
    else this match {
      case Param(_) => throw new RuntimeException("bordel de merde") //; new Read[T](repr(this).name)(mym.asInstanceOf[repr[T]])
      case _        => this.propagate((d: AST[T]) => d.deDag(usedTwice, repr, replaced))
    }
  }

  def nbit(cur: ProgData1[_], nbitLB: AstField[Int], tSymb: TabSymb[InfoNbit[_]], newFuns: TabSymb[ProgData2]): AST[T] = {
    val newthis = this.propagate((d: AST[T]) => d.nbit(cur, nbitLB, tSymb, newFuns))
    nbitLB += (newthis -> newthis.newNbitAST(nbitLB, tSymb, newFuns))
    newthis.setName(this.name); newthis
  }

  /**Compute the number of bits needed, using  mutable structures, that have  been previously updated. */
  def newNbitAST(nbitLB: AstField[Int], tSymb: TabSymb[InfoNbit[_]], newFuns: TabSymb[ProgData2]): Int = this.asInstanceOf[AST[_]] match {
    //   case Heead(a)          => List(nbitLB(a).head)
    //  case Taail(a)          => nbitLB(a).tail
    case Param(s) => tSymb(s).nb
    case Read(s)  => tSymb(s).nb
    //  case Coons(a, b)       => nbitLB(a).head :: nbitLB(b) //for ((k,v)<-nbitLB) println( k.toStringTree)     println( b.toStringTree)
  }

  /** recreates the whole structure   to avoid   side-effect. */
  def propagate(id1: bij2[_]): AST[T] = {
    val id = id1.asInstanceOf[bij2[T]] //if I put this type  bij2[T] directly for the parameter id1, it breaks covariance.
    def id2[T3]: bij2[T3] = d => id(d.asInstanceOf[AST[T]]).asInstanceOf[AST[T3]] //introduit des variables libres
    val newD = this.asInstanceOf[AST[_]] match {
      case Read(_)                 => this //throw  new RuntimeException("Deja dedagifié!" )
      case e: EmptyBag[_]          => e
      case Delayed(arg)            => id2(arg()) //the useless delayed node is supressed
      case e @ Heead(a)            => e.copy(arg = id2(a))(e.mym) //{ e.substitute(a,id2(a));e }//{e.arg = id2(a);e} //
      case e @ Taail(a)            => e.copy(arg = id2(a))(e.mym)
      case e @ Coons(a, a2)        => e.copy(arg = id2(a), arg2 = id2(a2))(e.mym)
      case e @ Call1(_, a)         => e.copy(arg = id2(a))(e.mym)
      case e @ Call2(_, a, a2)     => e.copy(arg = id2(a), arg2 = id2(a2))(e.mym)
      case e @ Call3(_, a, a2, a3) => e.copy(arg = id2(a), arg2 = id2(a2), arg3 = id2(a3))(e.mym)
    }; newD.setName(this.name); newD.asInstanceOf[AST[T]]
  }
  def concatElt: Boolean = this match {
    case _: EmptyBag[_] => true
    case _              => false
  }

 // def unfoldSpace(m:Machine ):List[ASTBt[_]] =  throw new RuntimeException("unfoldSpace must be applied on ASTLtonly ")
 // def unfoldSimplic(m:Machine ):ArrAst= throw new RuntimeException("unfoldSpace must be applied on ASTLtonly ")
  def unfoldTransfer(m:Machine ):ArrArrAst= throw new RuntimeException("unfoldSpace must be applied on ASTLtonly ")
  /**   Compute alignement with respect to input variables, and also constraint, given that v is the variable if we make a reduction*/
  def align(cs:TabConstr,v:String):iTabSymb[Array[Int]]= throw new RuntimeException("align must be applied on ASTLtonly ")
   /**True if "this" is a call to a fun2, whose first arg is a Tminus1 */
  def firstArgDelayed(muInstr:iTabSymb[List[Affect[_]]] ):Boolean=this match{
    case Call2(_, Read(s), _) =>
      val Array(rad,suf)=   s.split("\\$") //on separe le radical du suffixe
      muInstr(rad)(order(suf)) .exp.isInstanceOf[ASTB.Tminus1[_]]
    case _ => false
  }

  /** Defined non empty in ASTL */
   def redExpr = List.empty[AST[_]]
}

object AST {

  trait EmptyBag[T <: Dag[T]] extends Dag[T] { def inputNeighbors: List[T] = List.empty; }
  trait Singleton[T <: Dag[T]] extends Dag[T] { def arg: T; def inputNeighbors: List[T] = List(arg) }
  trait Doubleton[T <: Dag[T]] extends Dag[T] { def arg: T; def arg2: T; def inputNeighbors: List[T] = List(arg, arg2) }
  trait Tripleton[T <: Dag[T]] extends Dag[T] { def arg: T; def arg2: T; def arg3: T; def inputNeighbors: List[T] = List(arg, arg2, arg3) }
  trait Neton[T <: Dag[T]] extends Dag[T] { def args: List[T]; def inputNeighbors: List[T] = args  }

  private var nameCompteur: Int = 0

  def getCompteur: Int = { nameCompteur += 1; nameCompteur }
  def checkName2(): String = "_aux" + AST.getCompteur

  type bij2[U] = AST[U] => AST[U]
  case class Coons[Thead, Ttail](arg: AST[Thead], arg2: AST[Ttail])(implicit n: repr[(Thead, Ttail)]) extends AST[(Thead, Ttail)] with Doubleton[AST[_]] //{ def setArg(a: AST[_]) = arg = a.asInstanceOf[AST[Thead]]; def setArg2(a: AST[_]) = arg2 = a.asInstanceOf[AST[Ttail]] }
  case class Heead[Thead](arg: AST[(Thead, _)])(implicit n: repr[Thead]) extends AST[Thead] with Singleton[AST[_]] //{ def setArg(a: AST[_]) = arg = a.asInstanceOf[AST[Tuple2[Thead, _]]]; }
  case class Taail[Ttail](arg: AST[(_, Ttail)])(implicit n: repr[Ttail]) extends AST[Ttail] with Singleton[AST[_]] //{ def setArg(a: AST[_]) = arg = a.asInstanceOf[AST[Tuple2[_, Ttail]]]; }
  abstract class Fundef[+T](val namef: String, var body: AST[_], val p: Param[_]*) extends Named //no need to store the type of f's body at the level of fundef
  case class Fundef0[+To1](override val namef: String, arg: AST[To1]) extends Fundef[To1](namef, arg)
  case class Fundef1[+Ti1, +To1](override val namef: String, arg: AST[To1], p1: Param[Ti1]) extends Fundef[To1](namef, arg, p1)
  case class Fundef2[+Ti1, +Ti2, +To1](override val namef: String, arg: AST[To1], p1: Param[Ti1], p2: Param[Ti2]) extends Fundef[To1](namef, arg, p1, p2)
  case class Fundef3[+Ti1, +Ti2, +Ti3, +To1](override val namef: String, arg: AST[To1], p1: Param[Ti1],
                                             p2: Param[Ti2], p3: Param[Ti3]) extends Fundef[To1](namef, arg, p1, p2, p3)
  //on peut pas utiliser fundefn, car faudrait savoir a l'avance le nombre de paramétres, pour maj l'environnement.
  case class Fundefn[Ti1, To1](override val namef: String, arg: AST[To1], pn: Param[Ti1]*)(implicit n: repr[To1])
    extends Fundef[To1](namef, arg, pn: _*)
  case class Param[+T](nameP: String)(implicit n: repr[T]) extends AST[T] with EmptyBag[AST[_]] { name = nameP; }
  /** Replace call1, call2, call3, after the nbit stage */
  abstract class Call[T](val f: Fundef[T], val args: AST[_]*)(implicit n: repr[T]) extends AST[T]
  //final case class Multop[L <: Locus, R1 <: Ring, R2 <: Ring](op: Seq[ASTB[R1]] => ASTB[R2], var args: Seq[ASTLtrait[L, R1]], m: repr[L], n: repr[R2])
  //   extends ASTL[L, R2]()(repr.nomLR(m,n)) with Neton[AST[_]] { def setArgs(a: Seq[AST[_]]) = args = a.asInstanceOf[Seq[ASTLtrait[L, R1]]] }
  case class Call1[Ti1, To1](override val f: Fundef1[Ti1, To1], arg: AST[_ <: Ti1])(implicit n: repr[To1])
    extends Call[To1](f, arg) with Singleton[AST[_]]
  case class Call2[Ti1, Ti2, To1](override val f: Fundef2[Ti1, Ti2, To1], arg: AST[_ <: Ti1], arg2: AST[_ <: Ti2])(implicit n: repr[To1])
    extends Call[To1](f, arg, arg2) with Doubleton[AST[_]]
  case class Call3[Ti1, Ti2, Ti3, To1](override val f: Fundef3[Ti1, Ti2, Ti3, To1], arg: AST[_ <: Ti1], arg2: AST[_ <: Ti2], arg3: AST[_ <: Ti3])(implicit n: repr[To1])
    extends Call[To1](f, arg, arg2, arg3) with Tripleton[AST[_]]
  case class Read[T](which: String)(implicit m: repr[T]) extends AST[T]() with EmptyBag[AST[_]]
  case class Delayed[T](_arg: () => AST[T])(implicit m: repr[T]) extends AST[T]() with Singleton[AST[_]] { lazy val arg: AST[_] = { /* _arg().user+=this;*/ _arg() } }
  //on se sert de DELAYED que dans ASTL, donc on va directement l'y mettre.
  //def delayed3[L<:Locus,R<:Ring](_arg: => AST[Tuple2[L,R]])(implicit m: repr[Tuple2[L,R]])   = { lazy val delayed4 = _arg with AST2[L,R];new Delayed(() => delayed4) }

}

