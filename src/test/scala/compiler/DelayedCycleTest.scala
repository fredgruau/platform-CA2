package compiler

import AST._
import ASTL.delayedL
import Circuit.hexagon
import compiler.SpatialType.IntV
import org.scalatest.FunSuite

class DelayedCycleTest extends FunSuite {
  test("simple cycle") {
    val testCycle: Circuit[V, SI] = new CircuitCycleLayer2()
    testCycle.compile(Circuit.hexagon);
  }
}

//[SI](-2,3)
/** Builds a cycle in the DAG */
class CycleLayer2(nbit: Int)(implicit m: repr[V]) extends Layer[(V, SI)](nbit, "global") with ASTLt[V, SI] {
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


