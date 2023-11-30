package progOfmacros

import compiler.B
import compiler.AST._
import compiler.SpatialType.{BoolVe, _}
import compiler.ASTBfun.{addRedop, andRedop, minSignRedop, orRedop, p, redop, xorRedop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.ASTLt._
import compiler.Circuit.hexagon
import compiler._
import progOfmacros.Compute._
import compiler.SpatialType._
import progOfmacros.RedSwrapper.border

object Grad {

  /** macro that does all the computation needing the distance  From an IntV, computes the gradient sign, sloplt
   * which is true if the Vertice is nearer to the source than its neighbor
   * and the delta to be added to maintain it as a distance when the source is moving.
   * Also computes level which is true when the neihgbors are equal, and gap which is true if on edge
   * where the gradient is 4 in absolute value, which makes it impossible to decide the slope sign.
   * The vortex can be computed in a second step.
   * */
  val slopeDeltaDef: Fundef1[(V, SI), ((T[V, E], B), ((V, SI), ((E, B), (E, B))))] = {
    val d = pL[V, SI]("dis")
    val dopp = -d
    val se: IntVe = send(List(d, d, d, dopp, dopp, dopp)) //we  apply an opp on distances comming from the center.
    val grad3: IntE = reduce(addRedop[SI].asInstanceOf[redop[SI]], transfer(se)) //the trick here is to do the expensive operation (add) only on the three edges locus, instead of the 6 Ve transfer
    val gap: BoolE = eq0(grad3 + 4) //  gap is true iff the two neighbors cannot be compared
    val grad6: IntEv = send(List(-grad3, grad3))
    val slopEv: BoolEv = ltSI(grad6) //when sending back the result to EV, we have to invert again towards the center
    val slop: BoolVe = cond(chip.borderVe.df, transfer(slopEv), false) //faut definir ckispasse au bord. we put zero if unedfined
    val level: BoolE = ~reduce(orRedop[B], slopEv) //its equal if it is neither lt nor gt
    val delta: IntV = reduce(minSignRedop, sign(extend(4, transfer(grad6)) + 2)) //we need to add 2, using one more bit, in order to add modulo 16 and not 8
    //show(opp) //breaks a cycle
    level.setName("level"); //vortex.setName("vortex")
    grad3.setName("grad");
    slop.setName("slop");
    delta.setName("delta");
    Fundef1("grad.slopDelta", Cons(slop, Cons(delta, Cons(level, gap))), d)
  }

  /** Calls boolgrad, and separate the four results. */
  def slopDelta(d: IntV): (BoolVe, IntV, BoolE, BoolE) = {
    val r = Call1(slopeDeltaDef, d);
    val e1 = new Heead(r) with BoolVe
    val t = new Taail(r)
    val e2 = new Heead(t) with IntV
    val t2 = new Taail(t)
    val e3 = new Heead(t2) with BoolE
    val e4 = new Taail(t2) with BoolE
    (e1, e2, e3, e4)
  }
}
