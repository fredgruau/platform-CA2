package prog
//import compiler.ASTB._
import compiler.ASTL._
import macros.ASTLfun._
import compiler.ProgData.hexagon

import compiler._
class Dist(val source: BoolV) extends Layer[V, SI](3) {
  val level = elem(2, this); render(level)
  /*
  val tepred = transfer(e(pred))
  val grad: IntvE =  tepred - sym(tepred)  ; //should use opp to make only one subtraction, we need to adress selectively the two neighbors of an edge.
  val greater: BoolvE = gt(grad); render (greater)
//  val greaterOptimized:BoolvE=  notNull(tepred & v(mstb(xorR(tepred))))  //same as greater, but cost in gates is diminished!

  // val next= addL(pred,extend(3,cond(source, sign(opp(pred)), minR(transfer(sign(  addL(grad,const[T[E,V],SI](c,ConstInt(-2,3)))))))))
   val next =    pred + extend(3, cond(source, sign(- pred) , minR(transfer(sign( grad - 2 ) ))))
//  val nextOld = delayedL(  pred | cond(source, - pred  , minR(transfer( grad   ))))
   */ 
  val (slope, delta) = slopeDelta(pred)
  val next = this + cond(source, sign(-pred), delta)

 // val temp: BoolfV = xorR2(transfer(slope)) ;  val vortex: BoolF = orR(transfer(temp));   bugif(vortex);
  render(slope)
}

/**returns a constant layer. */
class ConstLayer[L <: Locus, R <: Ring](nbit: Int)(implicit m: repr[L], n: repr[R]) extends Layer[L, R](nbit) {
  val next = ~this //yes
}
 
class TestDist extends Circuit[V, SI](Dist.myInput) {
  val src = new ConstLayer[V, B](1)
  val dist = new Dist(src )
  def computeRoot = dist
}

//[SI](-2,3)
/** Builds a cycle in the DAG*/
class CycleLayer(nbit: Int)(implicit m: repr[V]) extends Layer[V, SI](nbit) {
  lazy val x: IntV = (next + pred);
  val next = delayedL(x);
}

object Dist { //  def g[L<:Locus](t:AST[L,B])(implicit m : repr[L]) = m.name; exemple de implicit que je conserve.
  val myInput=p[V, B]("input")
  def main(args: Array[String]) {
    val t: BoolV = true
    val testDist = new TestDist()
    // testDist.substitute(testDist.src,const[V,B](True[B] ))
    testDist.compile( hexagon //    List((testDist.src, t)) //this does a substitution.
    );
    val testCycle = new Circuit[V, SI]() { val chip = new CycleLayer(3); def computeRoot = chip.next }
    //testCycle.compile();

  }

}