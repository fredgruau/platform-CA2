package progOfCA

import compiler.SpatialType._
import compiler.AST._
import compiler.ASTBfun.{addRedop, andRedop, eqSI, minSignRedop, orRedop, p, redop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.ASTLt._
import compiler.Circuit.hexagon
import compiler._
import progOfmacros.Compute._
import compiler.SpatialType._

class Seed extends ConstLayer[V, B](1, "global") with DistT {
  show(this)
} //root classe compilable


class Dist(val source: Layer[(V, B)]) extends Layer[(V, SI)](3, "0") with ASTLt[V, SI] {
  //val level: BoolV = elem(2, this);
  val opp = -this
  val se: IntVe = send(List(this, this, this, opp, opp, opp)) //we  apply an opp on distances comming from the center.
  val grad3: IntE = reduce(addRedop[SI].asInstanceOf[redop[SI]], transfer(se)) //the trick here is to do the expensive operation (add) only on the three edges locus, instead of the 6 Ve transfer
  val gap: BoolE = unop(eqSI, grad3 + 4) //the two neighbors cannot be compared if gap is true
  val grad6: IntEv = send(List(-grad3, grad3)) //when sending back the result, we have to invert again towards the center
  val lt: BoolVe = transfer(ltSI(grad6))
  val eq: BoolE = ~reduce(orRedop[B], transfer(lt)) //its equal if it is neither lt nor gt
  val delta: IntV = reduce(minSignRedop, sign(extend(4, transfer(grad6)) + 2)) //we need to add 2, using one more bit, in order to add modulo 16 and not 8
  show(opp) //breaks the cycle
  val next: ASTLt[V, SI] = this + cond(source.asInstanceOf[BoolV], sign(opp), delta) //faudrait en faire une macro qui prends delta, source et dist et renvoie distNext
  val vortex: BoolF = reduce(andRedop[B], transfer(clock(lt) ^ anticlock(lt))); //faudrait en faire une marco
  //bugif(vortex) //rajoute l'instruction bugif dans la liste des instructions de slope.
  // val test= vortex |   andR(transfer(temp5)) ;  slope.bugif(test)
  // show(tr,grad3,grad6,deltaAjust)
  show(lt, eq, vortex, gap)

  /*// val delta: IntV = minR(transfer(sign(grad + -2)))
  val tepred = transfer(e(pred))
  val grad: IntvE =  tepred - sym(tepred)  ; //should use opp to make only one subtraction, we need to adress selectively the two neighbors of an edge.
  val greater: BoolvE = gt(grad); render (greater)
//  val greaterOptimized:BoolvE=  notNull(tepred & v(mstb(xorR(tepred))))  //same as greater, but cost in gates is diminished!
  // val next= addL(pred,extend(3,cond(source, sign(opp(pred)), minR(transfer(sign(  addL(grad,const[T[E,V],SI](c,ConstInt(-2,3)))))))))
   val next =    pred + extend(3, cond(source, sign(- pred) , minR(transfer(sign( grad - 2 ) ))))
//  val nextOld = delayedL(  pred | cond(source, - pred  , minR(transfer( grad   ))))
   //a decommenter un peu plus tard pour
   1-tester les reduction T
   2- mettre en place bugif
  val temp: BoolfV = clock(tslope)
  val temp2: BoolfV = anticlock(tslope)
     val vortex: BoolF = andR(transfer(xor(temp, temp2))); //faudrait en faire une marco
    vortex.setName("vortex");  bugif(vortex) //rajoute l'instruction bugif dans la liste des instructions de slope.
  // val test= vortex |   andR(transfer(temp5)) ;  slope.bugif(test)
    // ceci provoque bien l'erreur attendue java.lang.RuntimeException: Debug exp is allzero=>not usable for compute
    //ca montre que debug ne peut etre réutilisé.
 */

  //val next: ASTLt[V, SI] = this + cond(source.asInstanceOf[BoolV], sign(-this), delta) //faudrait en faire une macro qui prends delta, source et dist et renvoie distNext
  // val temp: BoolfV = xorR2(transfer(slope)) ;  val vortex: BoolF = orR(transfer(temp));   bugif(vortex);
}

trait DistT {
  self: Layer[(V, B)] => //adds a distance to a LayerV todo, it should also limit its movement
  val dist = new Dist(self);
  show(dist);
}

/** we here only update the distance */
class Dist2(val source: Layer[(V, B)]) extends Layer[(V, SI)](3, "0") with ASTLt[V, SI] {
  /*val level: BoolV = elem(2, this);*/
  val grad: IntVe = neighbors(this) - e(this)
  val lt: BoolVe = ltSI(grad)
  val eq: BoolE = ~reduce[E, V, B](orRedop[B], transfer(lt)) //its equal if it is neither lt nor gt
  val delta: IntV = reduce(minSignRedop, sign(extend(4, grad) + 2)) //we need to add 2, using one more bit, in order to add modulo 16 and not 8
  val next: ASTLt[V, SI] = this + cond(source.asInstanceOf[BoolV], sign(-this), delta) //faudrait en faire une macro qui prends delta, source et dist et renvoie distNext
  show(lt, eq)
}

/** contains show(dist) otherwise, class Dist is not compiled at all, because not used from the root */
trait Dist2T {
  self: Layer[(V, B)] => //adds a distance to a LayerV todo, it should also limit its movement
  val dist = new Dist2(self);
  show(dist);

}

