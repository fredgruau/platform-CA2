package progOfCA

import compiler.AST.{Layer, p}
import compiler.ASTL._
import compiler.Circuit.hexagon
import compiler.{AST, ASTLt, B, Circuit, F, V}
import progOfmacros.SReduce._

/** Simple growth one of the most simple circuit that can be conceived, used for debug */
class Grow extends Layer[(V, B)](1, "global") with ASTLt[V, B] {
  // val GrowE= existV2E(this);  val next: BoolV = existE2V(GrowE)
  val next: BoolV = neighborhood(this)
  next.setName("growNext")
  show(this) //shown field will get the name "grow", because we did grow=new Grow
  show(next)
}

// implement the intermediate stage in main, so that we have name variables as 2D arrays.
/*class GrowDec extends Layer[(V, B)](1,"global") with ASTLt[V, B] {
  // val GrowE= existV2E(this);  val next: BoolV = existE2V(GrowE)

  val neighbEE: BoolE = existV2E(this)
  show(neighbEE)
  val next: BoolV = existE2V(neighbEE)
  show(this)
}

class GrowF extends Layer[(F, B)](1,"global") with ASTLt[F, B] {
  val next: BoolF = neighborhoodfe(this)
  show(this)
}

/** uses the blob to grow voronoi region stoping the growth just before merge happens */
class GrowVor() extends Layer[(V, B)](1,"global") with ASTLt[V, B] with BlobV {
  val next: BoolV = neighborhood(this) & (~meetV) & (~existE2V(meetE)) //only radius 0 computation, because communication is handled in macro
  show(this)
  show(meetE)
  show(meetV)
}*/

/** Code for compiling Grow */
object Grow extends App {
  new Circuit[V, B]() {

    val grow = new Grow().asInstanceOf[ASTLt[V, B]];

    def computeRoot = grow //will be the name of this. if we print this in class Grow
  }.compile(hexagon)
}

class Foo {
  def hello(name: String): String = "Hello there, %s".format(name)
}


/*object GrowDec extends App {
  new Circuit[V, B]() {
    val grow = new GrowDec();

    def computeRoot: BoolV = grow
  }.compile(hexagon)
}

object GrowF extends App {
  new Circuit[F, B]() {
    val grow = new GrowF();

    def computeRoot: BoolF = grow
  }.compile(hexagon)
}

/** Code for compiling Growvor */
object GrowVor extends App {
  new Circuit[V, B]() {
    val growVor = new GrowVor();

    def computeRoot: BoolV = growVor
  }.compile(hexagon)
}*/






