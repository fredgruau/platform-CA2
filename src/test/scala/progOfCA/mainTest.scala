package progOfCA

import compiler.AST._
import compiler.ASTL._
import compiler.Circuit.hexagon
import compiler.{ASTLt, B, Circuit, V}
import progOfmacros.SReduce.{existE2V, neighborhood}
import org.scalatest
import org.scalatest.{BeforeAndAfter, FunSuite}

class mainTest extends FunSuite with BeforeAndAfter {
  test("main concatR, broadcast, elem") {

    new Circuit[V, B]() {
      val id = new DisguisedIdentity();

      def computeRoot: BoolV = id
    }.compile(hexagon)
  }
}

/** test concatR with elem */
class DisguisedIdentity() extends Layer[(V, B)](1, "global") with BlobV {
  val next: BoolV = elem(0, concatR(e(this))) //this is in fact the identity
  show(this)
}
