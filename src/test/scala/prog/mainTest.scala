package prog

import compiler.AST._
import compiler.ASTL._
import compiler.Circuit.hexagon
import compiler.{ASTLt, B, Circuit, V}
import macros.SReduce.{existE2V, neighborhood}
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

/** uses the blob to grow voronoi region stoping the growth just before merge happens */
class DisguisedIdentity() extends Layer[(V, B)](1) with BlobV {
  val next: BoolV = elem(0, concatR(e(this))) //this is in fact the identity
  show(this)
}
