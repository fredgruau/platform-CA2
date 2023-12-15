package progOfCA

import compiler.ASTLfun._
import compiler.AST._
import compiler.ASTL._
import compiler.Circuit.hexagon
import compiler.SpatialType.{BoolV, UintV}
import compiler.{ASTLt, B, Circuit, V}
import org.scalatest
import org.scalatest.{BeforeAndAfter, FunSuite}

/*
class mainTest extends FunSuite with BeforeAndAfter {
  test("main concatR, broadcast, elem") {

    new Circuit[V, B]() {
      val id = new DisguisedIdentity();

      def computeRoot: BoolV = id
    }.compile(hexagon)
  }
}

/** test concatR with elem */
class DisguisedIdentity() extends Layer[(V, B)](1, "global") with Topo {
  val next: BoolV = elt(0, concatR(e(this)).asInstanceOf[UintV]) //this is in fact the identity
  show(this)
}*/
