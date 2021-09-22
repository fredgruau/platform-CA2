package prog

//import compiler.ASTB._

import compiler.AST.Layer2
import compiler.ASTL._
import compiler.Circuit.hexagon
import compiler._
import macros.ASTLfun._

class Dist2(val source: BoolV) extends Layer2[(V, SI)](3) with ASTLt[V, SI] {
  val level: BoolV = elem(2, this);
  //render2(level)
  /*
  val tepred = transfer(e(pred))
  val grad: IntvE =  tepred - sym(tepred)  ; //should use opp to make only one subtraction, we need to adress selectively the two neighbors of an edge.
  val greater: BoolvE = gt(grad); render (greater)
//  val greaterOptimized:BoolvE=  notNull(tepred & v(mstb(xorR(tepred))))  //same as greater, but cost in gates is diminished!
  // val next= addL(pred,extend(3,cond(source, sign(opp(pred)), minR(transfer(sign(  addL(grad,const[T[E,V],SI](c,ConstInt(-2,3)))))))))
   val next =    pred + extend(3, cond(source, sign(- pred) , minR(transfer(sign( grad - 2 ) ))))
//  val nextOld = delayedL(  pred | cond(source, - pred  , minR(transfer( grad   ))))
   */
  val (slope, delta) = slopeDelta(this)
  val tslope = transfer(slope)
  val temp: BoolfV = clock(tslope)
  val temp2: BoolfV = anticlock(tslope)
  val vortex: BoolF = andR(transfer(xor(temp, temp2)));
  vortex.setName("vortex")
  // val test= vortex |   andR(transfer(temp5)) ;  slope.bugif(test)
  // ceci provoque bien l'erreur attendue java.lang.RuntimeException: Debug exp is allzero=>not usable for compute
  //ca montre que debug ne peut etre réutilisé.
  bugif2(vortex) //rajoute l'instruction bugif dans la liste des instructions de slope.
  val next: ASTLt[V, SI] = this + cond(source, sign(-this), delta)
  // val temp: BoolfV = xorR2(transfer(slope)) ;  val vortex: BoolF = orR(transfer(temp));   bugif(vortex);
  render2(slope)
}

/** returns a constant layer. */
class ConstLayer2[L <: Locus, R <: Ring](nbit: Int)(implicit m: repr[L], n: repr[R]) extends Layer2[(L, R)](nbit) with ASTLt[L, R] {
  val next: ASTLt[L, R] = delayedL(~this) //yes
}

class TestDist2 extends Circuit[V, SI](Dist2.myInput) {
  val src = new ConstLayer2[V, B](1)
  val dist = new Dist2(src)

  def computeRoot: ASTLt[V, SI] = dist
}

//[SI](-2,3)
/** Builds a cycle in the DAG */
class CycleLayer2(nbit: Int)(implicit m: repr[V]) extends Layer2[(V, SI)](nbit) with ASTLt[V, SI] {
  lazy val x: IntV = next + pred.asInstanceOf[ASTLt[V, SI]]
  val next: ASTLt[V, SI] = delayedL(x)
}

object Dist2 { //  def g[L<:Locus](t:AST[L,B])(implicit m : repr[L]) = m.name; exemple de implicit que je conserve.
  /** fake input  */
  val myInput: AST.Param[(V, B)] with ASTLt[V, B] = p[V, B]("input")

  def main(args: Array[String]) {
    //val t: BoolV = true
    val testDist2 = new TestDist2()
    // testDist.substitute(testDist.src,const[V,B](True[B] ))
    testDist2.compile2(hexagon //    List((testDist.src, t)) //this does a substitution.
    )
    //val testCycle: Circuit[V, SI] = new Circuit[V, SI]() { val chip = new CycleLayer(3); def computeRoot: ASTLt[V, SI] = chip.next }
    //testCycle.compile();

  }

}