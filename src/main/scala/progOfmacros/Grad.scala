package progOfmacros

import compiler.B
import compiler.AST._
import compiler.SpatialType.{BoolEv, BoolVe, _}
import compiler.ASTBfun.{addRedop, andRedop, derivative, minSignRedop, orRedop, p, redop, uI2SI, xorRedop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.ASTLt._
import compiler.Circuit.hexagon
import compiler._
import progOfmacros.Compute._
import progOfmacros.Wrapper.{borderS, not, segment1}

object Grad {

  /** macro that does all the computation needing the distance  From an IntV, computes the gradient sign, slopgt
   * which is true on the side where the Vertice has a higher integer value, (so, further  from the source than its neighbor)
   * and the delta to be added to maintain it as a distance when the source is moving.
   * Also computes level which is true when the neihgbors are equal, and gap which is true if on edge
   * where the gradient is 4 in absolute value, which makes it impossible to decide the slope sign.
   * The vortex can be computed in a second step.
   * */
  val slopeDeltaDef: Fundef1[(V, SI), ((T[V, E], B), ((V, SI), ((E, B), (E, B))))] =  {
    val d = pL[V, SI]("dis")
    val dopp = -d
    val se: IntVe = send(List(d, d, d, dopp, dopp, dopp)) //we  apply an opp on distances comming from the center.
    val grad3: IntE = reduce(addRedop[SI].asInstanceOf[redop[SI]], transfer(se)) //the trick here is to do the expensive operation (add) only on the three edges locus, instead of the 6 Ve transfer
    val gap: BoolE = eq0(grad3 + 4) //  gap is true iff the two neighbors cannot be compared
    val grad6: IntEv = send(List(-grad3, grad3))
    val slopEv: BoolEv = ltSI(grad6) //when sending back the result to EV, we have to invert again towards the center
    val slopgt: BoolVe = cond(chip.borderVe.df, transfer(slopEv), false) //faut definir ckispasse au bord. we put zero if unedfined
    val level: BoolE = ~reduce(orRedop[B], slopEv) //its equal if it is neither lt nor gt
    val delta: IntV = reduce(minSignRedop, sign(extend(4, transfer(grad6)) + 2)) //we need to add 2, using one more bit, in order to add modulo 16 and not 8
    //show(opp) //breaks a cycle
    level.setName("level"); //vortex.setName("vortex")
    grad3.setName("grad");
    slopgt.setName("slop");
    delta.setName("delta");
    Fundef1("grad.slopDelta", Cons(slopgt, Cons(delta, Cons(level, gap))), d)
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

  /** former way of computing together both lt and eq, may be not so bad, but eq has to be used, which is prone to error
   * because quite often we are only interested by lt
   * */
  val slopeLtDef: Fundef1[(V, UI), ((T[E, V], B),  (E,B))] =  {
    val d = pL[V, UI]("dis")
    //val d=uI2SIL(d1)
    val dEv: UintEv = transfer(e(d))//send(List(d, d, d, d,d,d)) //we  apply an opp on distances comming from the center.
    dEv.setName("dev")
    //val grad3: IntE = reduce(addRedop[SI].asInstanceOf[redop[SI]], transfer(se)) //the trick here is to do the expensive operation (add) only on the three edges locus, instead of the 6 Ve transfer
    val lt:BoolE=ltUiEdge(dEv);lt.setName("lt")
    val eq:BoolE=eqUiEdge(dEv);eq.setName("eq")
    val gt:BoolE= ~(lt|eq);gt.setName("gt")
    val slopEv: BoolEv = send(List(gt,lt)) //when sending back the result to EV, we have to invert again towards the center
    slopEv.setName("slopeEv")
    Fundef1("grad.slopLt", Cons(slopEv, eq), d)
    Fundef1("grad.slop", Cons(slopEv, eq), d)
  }

  /** Calls slopeLt, and separate the two results. */
  def slopeLt(d: UintV): (BoolEv,  BoolE) = {
    val r = Call1(slopeLtDef, d);
    val slopeLtEv = new Heead(r) with BoolEv
    val level = new Taail(r)with BoolE
    (slopeLtEv, level)
  }
  /** macro that, computes Lt, optimally,
   * lt  is true  on the side where the Vertice has a lower integer value (used for priority)
   * lt is needed for comparison of priority, when doing mutex tournament
   * */
  val ltDef: Fundef2[(V, UI),(E, UI), (T[E, V], B)] =  {
    /** main variable that we want to compare */
    val d = pL[V, UI]("dis")
    /** segment is used for computing eq, so we  compute it separately*/
    val segmentOf1 =pL[E, UI]("segment")
    /** this was also computed when xor was computed, but we save memory by recomputing it, and it is small */
    val dEv: UintEv = transfer(e(d))
    /** binop edge that forget the second component */
    val devLeft:UintE= firstEdge(dEv);
    /** true if both values are different */
    val diff= elt(0,segmentOf1)
    val lt1: BoolE =neq(unop(derivative, segmentOf1)&devLeft);
    /** strictly greater means not strictly smaller, and different */
    val gt1:BoolE= ~lt1 & diff;
    val lt: BoolEv = send(List(lt1,gt1))
    Fundef2("grad.lt", lt, d,segmentOf1)
  }

  /** Calls pure lt, result will be true on the side of the cell having smallest value  */
  def lt(d: UintV,s:UintE)(implicit n: repr[B],l:repr[T[E,V]]): BoolEv = {
    new Call2[(V,UI),(E,UI),(T[E, V], B)] (ltDef, d,s)with BoolEv
  }

  import progOfmacros.Comm._

 /** same as lt, but with respect to Ef, and apex */

  val ltDefApex: Fundef2[(V, UI),(E, UI), (T[E, F], B)] =  {
    /** main variable that we want to compare */
    val d = pL[V, UI]("dis")
    /** segment is used for computing eq, so we  compute it separately*/
    val segmentOf1 =pL[E, UI]("segment")
    /** this was already computed when xor was computed, but we save memory by recomputing it, and it is small */
    val dEf: UintEf = apexEui(f(d))
    /** binop edge that forget the second component */
    val devLeft:UintE= firstEdge(dEf);
    /** true if both values are different */
    val diff= elt(0,segmentOf1)
    val lt1: BoolE =neq(unop(derivative, segmentOf1)&devLeft);
    /** strictly greater means not strictly smaller, and different */
    val gt1:BoolE= ~lt1 & diff;
    val lt: BoolEf = send(List(lt1,gt1))
    Fundef2("grad.lt", lt, d,segmentOf1)
  }

  /** Calls pure lt, result will be true on the side of the cell having smallest value  */
  def ltApex(d: UintV,s:UintE)(implicit n: repr[B],l:repr[T[E,V]]): BoolEf = {
    new Call2[(V,UI),(E,UI),(T[E, F], B)] (ltDefApex, d,s)with BoolEf
  }




  /** yet another way on computing lt, on which we spent a bit of time! */
  val ltDefOld: Fundef1[(V, UI), (T[E, V], B)] =  {
    val d = pL[V, UI]("dis")
    //val d=uI2SIL(d1)
    val dEv: UintEv = transfer(e(d))//send(List(d, d, d, d,d,d)) //we  apply an opp on distances comming from the center.
    dEv.setName("dev")
    //val grad3: IntE = reduce(addRedop[SI].asInstanceOf[redop[SI]], transfer(se)) //the trick here is to do the expensive operation (add) only on the three edges locus, instead of the 6 Ve transfer
    val lt:BoolE=ltUiEdge(dEv);lt.setName("lt")
    val eq:BoolE=eqUiEdge(dEv);eq.setName("eq")
    val gt:BoolE= ~(lt|eq);gt.setName("gt")
    val slopEv: BoolEv = send(List(gt,lt)) //when sending back the result to EV, we have to invert again towards the center
    slopEv.setName("slopeEv")
    Fundef1("grad.slop", slopEv, d)
  }
  /** Calls pure slope, result will be true on the side of the cell having greater value  */
  def ltOld(d: UintV)(implicit n: repr[B],l:repr[T[E,V]]): BoolEv = {
    new Call1[(V,UI),(T[E, V], B)] (ltDefOld, d)with BoolEv
  }


}
