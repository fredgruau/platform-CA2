package progOfCA

import compiler.SpatialType._
import compiler.AST._
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.hexagon
import compiler._
import compiler.SpatialType._
import progOfmacros.Util.{randN12, randN6, randNext}
/** Layer implementing a random bit */
class Rand() extends Layer[(V, B)](1, "random") with ASTLt[V, B] {
  val next: BoolV = randNext(this) //randDef is used only here, no need for a wrapper!
  val randEdge: BoolVe = randN12(this)
  show(this, randEdge)
}

object Rand extends App {
  /** macro computing the next state of a random bit */


  new Circuit[V, B]() {
    val rand = new Rand();

    def computeRoot: BoolV = rand
  }.compile(hexagon)


}

