package compiler

import AST.Layer2
import ASTL.{IntV, delayedL}
import Circuit.hexagon
import macros.ASTLfun.p
import org.scalatest.FunSuite
import prog.TestDist2

class DelayedCycleTest extends FunSuite {
  test("simple cycle") {
    val testCycle: Circuit[V, SI] = new CircuitCycleLayer2()
    testCycle.compile2(Circuit.hexagon);
  }
}

//[SI](-2,3)
/** Builds a cycle in the DAG */
class CycleLayer2(nbit: Int)(implicit m: repr[V]) extends Layer2[(V, SI)](nbit) with ASTLt[V, SI] {
  //The DFS algo of DAG visite all Delayed node recursively as soon as they are created, because
  //the delayed expression is an input of the Delayed node
  lazy val x: IntV = next + pred.asInstanceOf[ASTLt[V, SI]]
  //upon inspection of memorize callProc, DFS search is launched  it will visite all Delayed node
  val next: ASTLt[V, SI] =
    delayedL(delayedL(x))
}

class CircuitCycleLayer2 extends Circuit[V, SI](p[V, B]("input")) {

  val cycle = new CycleLayer2(3)

  def computeRoot: ASTLt[V, SI] = cycle
}


