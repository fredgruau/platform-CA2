package progOfmacros

//import compiler._

import compiler.AST._
import compiler.ASTL._
import compiler.ASTB._
import compiler.ASTBfun.{Fundef3R, p}
import compiler._


/** Contains the code of locus function used as a layer of  building blocks of small bits of spatial operators, compiled with optimal perf. */
object Compute {

  val incDef: Fundef1[(V, SI), (V, SI)] = {
    val d = p[V, SI]("dis")
    val newd = inc(d)
    Fundef1("integer.inc", newd, d)
  }

  def callInc(d: IntV): IntV = {
    new Call1(incDef, d) with IntV;
  }


  /** From an IntV, computes the gradient sign, and the delta to be added to make it a distance
   * */
  val slopeDeltaDef: Fundef1[(V, SI), ((T[V, E], B), (V, SI))] = {
    //val x:IntV= p[V, SI]("dis")
    val d = p[V, SI]("dis")
    val s: IntVe = sende(List(d, d, d, -d, -d, -d))
    // val tepred = transfer(e(x))
    val tepred = transfer(s)
    //   val g: ASTLt[E, SI] = subESI(tepred)
    val g: ASTLt[E, SI] = addESI(tepred)
    val grad: IntEv = sendv(List(g, -g))
    //val grad: IntvE = tepred - sym(tepred)
    // TODO should use opp to make only one subtraction, we need to adress selectively the two neighbors of an edge.
    val slope: BoolVe = transfer(lt(grad))

    val delta: IntV = minR(transfer(sign(grad + -2)))
    //val temp: BoolfV = xorR2(tslope )
    grad.setName("grad");
    tepred.setName("tepred");
    slope.setName("slope");
    delta.setName("delta"); //vortex.setName("vortex")
    Fundef1("integer.grad", Cons(slope, delta), d)
  }

  /** Calls boolgrad, and separate the two results.  */
  def slopeDelta(d: IntV): (BoolVe, IntV) = {
    val r = Call1(slopeDeltaDef, d);
    (new Heead(r) with BoolVe, new Taail(r) with IntV)
  }


  /** Does only one or, which appear ridiciulously small for a macro, but that May avoid generating too many CaLoops */
  val orVdef: Fundef2[(V, B), (V, B), (V, B)] = {
    val b0 = p[V, B]("b0")
    val b1 = p[V, B]("b1")
    val r = b1 | b0
    Fundef2("orV", r, b0, b1)
  }

  def orV(b0: BoolV, b1: BoolV): BoolV = new Call2(orVdef, b0, b1) with BoolV


  val andVdef: Fundef2[(V, B), (V, B), (V, B)] = {
    val b0 = p[V, B]("b0")
    val b1 = p[V, B]("b1")
    val r = b1 & b0
    Fundef2("orV", r, b0, b1)
  }

  def andV(b0: BoolV, b1: BoolV): BoolV = new Call2(andVdef, b0, b1) with BoolV

  val andEdef: Fundef2[(E, B), (E, B), (E, B)] = {
    val b0 = p[E, B]("b0")
    val b1 = p[E, B]("b1")
    val r = b1 & b0
    Fundef2("orV", r, b0, b1)
  }

  def andE(b0: BoolE, b1: BoolE): BoolE = new Call2(andEdef, b0, b1) with BoolE


  val notEdef: Fundef1[(E, B), (E, B)] = {
    val b0 = p[E, B]("b0")
    val r = ~b0
    Fundef1("notE", r, b0)
  }

  def notE(b0: BoolE): BoolE = new Call1(notEdef, b0) with BoolE

}