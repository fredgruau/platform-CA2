package prog

import compiler.AST.{Layer, p}
import compiler.ASTL._
import compiler.Circuit.hexagon
import compiler.{AST, ASTLt, B, Circuit, V}
import macros.SReduce._

/** Simple growth one of the most simple circuit that can be conceived, used for debug */
class Grow extends Layer[(V, B)](1) with ASTLt[V, B] {
  val next: BoolV = neighborhood(this)
  show(this)
}

/** uses the blob to grow voronoi region stoping the growth just before merge happens */
class GrowVor() extends Layer[(V, B)](1) with ASTLt[V, B] with BlobV {
  val next: BoolV = neighborhood(this) & (~meetV) & (~existE2V(meetE)) //only radius 0 computation, because communication is handled in macro
  show(this)
  show(meetE)
  show(meetV)
}

/** Code for compiling Grow */
object Grow extends App {
  new Circuit[V, B]() {
    val grow = new Grow();

    def computeRoot: BoolV = grow
  }.compile(hexagon)
}

/** Code for compiling Growvor */
object GrowVor extends App {
  new Circuit[V, B]() {
    val growVor = new GrowVor();

    def computeRoot: BoolV = growVor
  }.compile(hexagon)
}






