package compiler
import compiler.AST._
import dataStruc.{DagNode, Named}
import compiler.Circuit._
import scala.collection._
import scala.collection.immutable.HashSet
import Circuit.AstPred

/**
 * Represent a field using an Abstract Syntax Tree using
 * Function definition, and calls, reading of variables, delaying of evaluation.
 * Reused to implement
 * 1- the AST of spatial  field (ASTL)
 * 2- the AST of arithmetic field(ASTB)
 *
 * @tparam T type of the expression
 * @param m parameter used to compute this type. */
abstract class AST[+T]()(implicit m: repr[T]) extends DagNode[AST[_]] with Named {


  val mym: repr[T] = m //if type of mym is set to repr[_] this allow covariance even if repr is not covariant
  /** system instruction can be associated to any spatial field, so as to be latter retrievable from the compiling method. */


  /** Builds the set of symbols which are read
   * do not consider layer, those represent memory cells to be loaded */
  def symbolsExcepLayers: immutable.HashSet[String] =
    this match {
      case Read(s) => if (isLayer(s)) HashSet() else HashSet(s)
      case Param(s) => HashSet(s)
      case l: Layer2[_] => HashSet() //HashSet(l.name)
      case _ => inputNeighbors.map(e => e.symbolsExcepLayers).foldLeft(HashSet.empty[String])((x, y) => x.union(y))
    }


  override def toString: String =

    this.asInstanceOf[AST[_]] match {
      case Read(s) => s
      case Param(s) => "Param " + s
      // case f: Fundef[_]      => "Fundef " + f.namef + " of param " + f.p.map(p => p.nameP).foldLeft("")(_ + ", " + _)
      case c: Call[_] => "Call " + c.f.namef + " " //  + mym.name
      case Heead(_) => "head"
      case Taail(_) => "tail"
      case Coons(_, _) => "cons"
      case Delayed(arg) => "Delayed"
      case l: Layer2[_] => "Layer2 " + this.name + ":" + mym.name
      case _ => throw new RuntimeException("merdouille")
  }

  /**
   * Transform a Dag of AST into a forest of trees, removes the delayed.
   * Treefy must be written for AST because At the start, we use Coons which are AST expression not being ASTLt[L,R]
   * * Important to specify that the L,R type of AST nodes is preserved, for type checking consistency
   * Surprisingly, when building ASTL explicitely, we need to drop the fact that the type is preserved, and go from ASTL[L,R] to ASTLg
   * Transform a Dag of AST into a forest of trees, removes the delayed.
   * *
   *
   * @param usedTwice dags which are used twice, or which need to be affected for some other reason.
   * @param repr      : representant of the equivalence class with respect to equal on case class hierarchy
   * @return the AST where expression used more than once are replaced by read.
   */
  def treeIfy(usedTwice: AstPred, repr: Map[AST[_], String]): AST[T] = {
    val rewrite = (d: AST[T]) => d.treeIfy(usedTwice, repr)
    if (usedTwice(this)) new Read[T](repr(this))(mym.asInstanceOf[repr[T]])
    else this.propagate(rewrite)
  }

  /**
   * @param id1 a bijection betwee AST
   * @return recreates the whole structure   to avoid   side-effect. because we build List, using Coons, Heead, Taail,
   *         the  Call can be of type AST and not ASTLt, as heead, and taail.  therefore we'd need to propagate on them
   */
  def propagate(id1: rewriteAST[_]): AST[T] = {
    val id = id1.asInstanceOf[rewriteAST[T]] //if I put this type  bij2[T] directly for the parameter id1, it breaks covariance.
    def id2[T3]: rewriteAST[T3] = d => id(d.asInstanceOf[AST[T]]).asInstanceOf[AST[T3]] //introduit des variables libres
    val newD = this.asInstanceOf[AST[_]] match {
      case Read(_) => this //throw  new RuntimeException("Deja dedagifié!" )
      case e: EmptyBag[_] => e
      //case Delayed(arg) => id2(arg()) //the useless delayed node is supressed Delayed are now ASTLt

      case e@Heead(a) => e.copy(arg = id2(a))(e.mym) //{ e.substitute(a,id2(a));e }//{e.arg = id2(a);e} //
      case e@Taail(a) => e.copy(arg = id2(a))(e.mym)
      case e@Coons(a, a2) => e.copy(arg = id2(a), arg2 = id2(a2))(e.mym)
      case e@Call1(_, a) =>
        val toto = e.copy(arg = id2(a))(e.mym)
        toto
      case e@Call2(_, a, a2) => e.copy(arg = id2(a), arg2 = id2(a2))(e.mym)
      case e@Call3(_, a, a2, a3) => e.copy(arg = id2(a), arg2 = id2(a2), arg3 = id2(a3))(e.mym)
    };
    newD.setName(this.name);
    newD.asInstanceOf[AST[T]]
  }


}

object AST {
  def isLayer(str: String) = str.charAt(0) == 'l' && str.charAt(1) == 'l'
  val isNotRead: AstPred = {
    case AST.Read(which) => false;
    case _ => true
  }
  val isCons: AstPred = {
    case Taail(_) | Heead(_) | Call1(_, _) | Call2(_, _, _) | Call3(_, _, _, _) => true;
    case _ => false
  }

  trait EmptyBag[T <: DagNode[T]] extends DagNode[T] {
    def inputNeighbors: List[T] = List.empty;
  }

  trait Singleton[T <: DagNode[T]] extends DagNode[T] {
    def arg: T;

    def inputNeighbors: List[T] = List(arg)
  }

  trait Doubleton[T <: DagNode[T]] extends DagNode[T] {
    def arg: T;

    def arg2: T;

    def inputNeighbors: List[T] = List(arg, arg2)
  }

  trait Tripleton[T <: DagNode[T]] extends DagNode[T] {
    def arg: T;

    def arg2: T;

    def arg3: T;

    def inputNeighbors: List[T] = List(arg, arg2, arg3)
  }

  trait Neton[T <: DagNode[T]] extends DagNode[T] {
    def args: List[T];

    def inputNeighbors: List[T] = args
  }


  type rewriteAST[U] = AST[U] => AST[U]
  type rewriteAST2 = AST[_] => AST[_]

  /** There is not ASTLt type for Coons.  */
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

  /**
   * The DFS algo of DAG visite recursively all Delayed node of an  AST  as soon as they are created, because
   * the delayed expression is an input of the Delayed node.
   *
   * @param _arg delayed expression   */
  case class Delayed[T](_arg: () => AST[T])(implicit m: repr[T]) extends AST[T]() with Singleton[AST[_]] {
    lazy val arg: AST[_] = {
      /* _arg().user+=this;*/ _arg()
    }
  }

  /** Delayed uses a trick found on the net, to have a call by name, together with a case class necessary to make the match */
  def delayed[T](_arg: => AST[T])(implicit m: repr[T]): AST[T] = {
    lazy val delayed = _arg;
    new Delayed[T](() => delayed)
  }

  //on se sert de DELAYED que dans ASTL, donc on va directement l'y mettre.
  //def delayed3[L<:Locus,R<:Ring](_arg: => AST[Tuple2[L,R]])(implicit m: repr[Tuple2[L,R]])   = { lazy val delayed4 = _arg with AST2[L,R];new Delayed(() => delayed4) }

  trait Strate2[T] {
    val pred: AST[T];
    val next: AST[T]
  }

  /**
   * @param nbit the number of bits
   * @tparam T
   * Unlike other constructors,  Layer is not defined as a case class,
   * otherwise equality between any two layer of identical number of bits would allways hold
   * Layer2 is an AST constructor, because it is used both in ASTL and ASTB
   * it is used to also stores system instructions.
   **/
  abstract class Layer2[T](val nbit: Int)(implicit m: repr[T]) extends AST[T]() with EmptyBag[AST[_]] with Strate2[T] {

    val v = 1
    /** the value at t, which  is represented as  the layer itself. */
    val pred: AST[T] = this



    /** needed to visite the next fields */
    override def other: List[AST[_]] = next :: super.other


    /** system instruction can be associated to any spatial field, so as to be latter retrievable from the compiling method. */
    private var sysInstr2: List[CallProc] = List.empty;

    protected def render2(v: AST[_]) = sysInstr2 ::= CallProc("show", List(), List(v))

    def bugif2(v: AST[_]) = sysInstr2 ::= CallProc("bug", List(), List(v))

    /**
     * nb callProc memo is re-created therefore its name is not precised
     *
     * @return
     */

    def systInstrs2: List[CallProc] = CallProc("memo", List(DataProg.lify(name)), List(next)) :: sysInstr2

    // def systInstrs2: List[CallProc] = CallProc("memo", List(name), List(next)) :: sysInstr2


  }
}

