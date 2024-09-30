package progOfCA

import compiler.SpatialType._
import compiler.AST._
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.hexagon
import compiler._
import compiler.SpatialType._
import progOfmacros.Util.{randE2, randN12, randNext}
/** Layer implementing a random bit */
class Rand() extends Layer[(V, B)](1, "random") with ASTLt[V, B]         {
  val next: BoolV = randNext(this) //randDef is used only here, no need for a wrapper!
  lazy val randDir: BoolVe = randN12(this) //only qpointRand uses this
  lazy val randSide: BoolEv = randE2(this) //only qpointRand uses this
  show(randSide)
  //show(this, randDir)
}

object Rand extends App {
  /** macro computing the next state of a random bit */


  new Circuit[V, B]() {
    val raaand = new Rand();

    def computeRoot: BoolV = raaand
  }.compile(hexagon)


}

