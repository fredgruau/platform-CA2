package progOfCA

import compiler.AST._
import compiler.ASTL._
import compiler.ASTLt._
import compiler.Circuit.hexagon
import compiler._
import progOfmacros.Compute._
import progOfmacros.SReduce._

/** adds a distance */
trait Dddist {
  self: Layer[(V, B)] =>
  val dist = new Dist(self)
  show(dist)
  show(dist.tslope) //this show must appear in class Dist, otherwise, class Dist is not compiled because not used from SRC
}

class Dist(val source: Layer[(V, B)]) extends Layer[(V, SI)](3, "0") with ASTLt[V, SI] {
  val level: BoolV = elem(2, this);
  /*
  val tepred = transfer(e(pred))
  val grad: IntvE =  tepred - sym(tepred)  ; //should use opp to make only one subtraction, we need to adress selectively the two neighbors of an edge.
  val greater: BoolvE = gt(grad); render (greater)
//  val greaterOptimized:BoolvE=  notNull(tepred & v(mstb(xorR(tepred))))  //same as greater, but cost in gates is diminished!
  // val next= addL(pred,extend(3,cond(source, sign(opp(pred)), minR(transfer(sign(  addL(grad,const[T[E,V],SI](c,ConstInt(-2,3)))))))))
   val next =    pred + extend(3, cond(source, sign(- pred) , minR(transfer(sign( grad - 2 ) ))))
//  val nextOld = delayedL(  pred | cond(source, - pred  , minR(transfer( grad   ))))
   */
  val (tslope, delta) = slopeDelta(this)
  // val tslope = transfer(slope)
  val temp: BoolfV = clock(tslope)
  val temp2: BoolfV = anticlock(tslope)
  // val vortex: BoolF = andR(transfer(xor(temp, temp2)));
  val vortex: BoolF = andR(transfer(xor(temp, temp2))); //faudrait en faire une marco
  vortex.setName("vortex")
  // val test= vortex |   andR(transfer(temp5)) ;  slope.bugif(test)
  // ceci provoque bien l'erreur attendue java.lang.RuntimeException: Debug exp is allzero=>not usable for compute
  //ca montre que debug ne peut etre réutilisé.
  bugif(vortex) //rajoute l'instruction bugif dans la liste des instructions de slope.
  val next: ASTLt[V, SI] = this + cond(source.asInstanceOf[BoolV], sign(-this), delta) //faudrait en faire une macro qui prends delta, source et dist et renvoie distNext
  // val temp: BoolfV = xorR2(transfer(slope)) ;  val vortex: BoolF = orR(transfer(temp));   bugif(vortex);
}

class Tdis extends ConstLayer[V, B](1, "global") with Dddist {}

object Dist extends App {



  val myInput: AST.Param[(V, B)] with ASTLt[V, B] = p[V, B]("input")
  new Circuit[V, B]() { //pour l'instant on teste sans parametres
    // new Circuit[V, SI](myInput) {
    val seed = new ConstLayer[V, B](1, "global") with Dddist {}

    def computeRoot: ASTLt[V, B] = seed
  }.compile(hexagon)
}

