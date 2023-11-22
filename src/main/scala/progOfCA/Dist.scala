package progOfCA

import compiler.AST._
import compiler.SpatialType.{BoolVe, _}
import compiler.ASTBfun.{addRedop, andRedop, minSignRedop, orRedop, p, redop, xorRedop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.ASTLt._
import compiler.Circuit.hexagon
import compiler.{B, _}
import progOfmacros.Compute._
import compiler.SpatialType._
import progOfCA.Dist.slopDelta
import progOfmacros.RedS.frontier

class Seed extends ConstLayer[V, B](1, "global") with DistT {
  show(this)
} //root classe compilable

object Dist {
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
    val slop: BoolVe = transfer(slopEv)
    val level: BoolE = ~reduce(orRedop[B], slopEv) //its equal if it is neither lt nor gt
    val delta: IntV = reduce(minSignRedop, sign(extend(4, transfer(grad6)) + 2)) //we need to add 2, using one more bit, in order to add modulo 16 and not 8
    //show(opp) //breaks a cycle
    level.setName("level"); //vortex.setName("vortex")
    grad3.setName("grad");
    slop.setName("slop");
    delta.setName("delta");
    Fundef1("integer.slopDelta", Cons(slop, Cons(delta, Cons(level, gap))), d)
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

class Dist(val source: Layer[(V, B)]) extends Layer[(V, SI)](3, "random") with ASTLt[V, SI] {
  val opp = -this
  val (sloplt: BoolVe, delta, level, gap) = slopDelta(this)
  val topoligne: BoolE = frontier(elt(2, this));
  val vortex: BoolF = andR(transfer(cac(xorRedop[B]._1, sloplt))) // andR( transfer(clock(sloplt) ^ anticlock(sloplt))); //transitive circular lt

  //  bugif(vortex) //rajoute l'instruction bugif dans la liste des instructions de slope.
  show(sloplt, delta, level, topoligne, vortex, gap)
  val next: ASTLt[V, SI] = this + cond(source.asInstanceOf[BoolV], sign(opp), delta) //faudrait en faire une macro qui prends delta, source et dist et renvoie distNext

}

trait DistT {
  self: Layer[(V, B)] => //adds a distance to a LayerV todo, it should also limit its movement
  val dist = new Dist(self);
  show(dist);
}


/** contains show(dist) otherwise, class Dist is not compiled at all, because not used from the root */
trait DistSimplerT {
  self: Layer[(V, B)] => //adds a distance to a LayerV todo, it should also limit its movement
  val dist = new DistSimpler(self);
  show(dist);

}

/** a simpler version of distance, which does not uses send */
class DistSimpler(val source: Layer[(V, B)]) extends Layer[(V, SI)](3, "0") with ASTLt[V, SI] {
  /*val level: BoolV = elem(2, this);*/
  val grad: IntVe = neighbors(this) - e(this)
  val lt: BoolVe = ltSI(grad)
  val eq: BoolE = ~reduce[E, V, B](orRedop[B], transfer(lt)) //its equal if it is neither lt nor gt
  val delta: IntV = reduce(minSignRedop, sign(extend(4, grad) + 2)) //we need to add 2, using one more bit, in order to add modulo 16 and not 8
  val next: ASTLt[V, SI] = this + cond(source.asInstanceOf[BoolV], sign(-this), delta) //faudrait en faire une macro qui prends delta, source et dist et renvoie distNext
  show(lt, eq)
}

