package progOfCA

import compiler.AST.{Layer, p}
import compiler.ASTL.{BoolV, _}
import compiler.Circuit.hexagon
import compiler.{AST, ASTLt, B, Circuit, E, F, V}
import progOfmacros.RedS.exist
import progOfmacros.SReduce._

/** Simple growth one of the most simple circuit that can be conceived, used for debug */
class Grow extends Layer[(V, B)](1, "global") with ASTLt[V, B] {
  val neighbEE: BoolE = exist(this);
  show(neighbEE) //pas besoin de faire intervenir defVe
  override val next: BoolV = exist(neighbEE) //  make use of defVe brough to us implicitely,
  // nb if overrid is not written, it does not work!
  show(this) //shown field will get the name "grow", because we set the name of root to arg(0).lowercase
  show(next)
}

class GrowF extends Layer[(V, B)](1, "global") with ASTLt[V, B] {
  val neighbFF: BoolF = exist(this); //no use of  defEv
  show(neighbFF)
  override val next: BoolV = exist(neighbFF) //  make use of defVf brough to us implicitely,nb if overrid is not written, it does not work!
  show(this) //shown field will get the name "grow", because we set the name of root to arg(0).lowercase
  show(next)
}

class GrowEF extends Layer[(E, B)](1, "global") with ASTLt[E, B] {
  // val neighbFF: BoolF = exist(this); //no use of defFe

  val broadcasted = f(this) //step 1 is broadcast
  val transfered = transfer(broadcasted) //step 2 is transfer
  val neighbFF = orRB(transfered) //(n,m,d) yzeté implicit killerest
  show(broadcasted)
  show(transfered)
  show(neighbFF) //uses defEf
  override val next: BoolE = exist(neighbFF) //  make use of defVe brough to us implicitely,nb if overrid is not written, it does not work!
  show(this) //shown field will get the name "grow", because we set the name of root to arg(0).lowercase
  show(next)
}

class GrowEV extends Layer[(E, B)](1, "global") with ASTLt[E, B] {
  // val neighbFF: BoolF = exist(this); //no use of defFe

  val broadcasted = v(this) //step 1 is broadcast
  val transfered = transfer(broadcasted) //step 2 is transfer
  val nv: BoolV = orRB(transfered) //(n,m,d) yzeté implicit killerest
  show(broadcasted)
  show(transfered)
  show(nv) //uses defEf
  override val next: BoolE = exist(nv) //  make use of defVe brough to us implicitely,nb if overrid is not written, it does not work!
  show(this) //shown field will get the name "grow", because we set the name of root to arg(0).lowercase
  show(next)
}


// implement the intermediate stage in main, so that we have name variables as 2D arrays.
class GrowDec extends Layer[(V, B)](1, "global") with ASTLt[V, B] {
  // val GrowE= existV2E(this);  val next: BoolV = existE2V(GrowE)

  val neighbEE: BoolE = existV2E(this)
  show(neighbEE)
  val next: BoolV = existE2V(neighbEE)
  show(this)
}

/** uses the blob to grow voronoi region stoping the growth just before merge happens */
class GrowVor() extends Layer[(V, B)](1,"global") with ASTLt[V, B] with BlobV {
  val next: BoolV = neighborhood(this) & (~meetV) & (~existE2V(meetE)) //only radius 0 computation, because communication is handled in macro
  show(this)
  show(meetE)
  show(meetV)
}

/** Code for compiling Grow */
/*object Grow extends App {
  new Circuit[V, B]() {

    val grow = new Grow().asInstanceOf[ASTLt[V, B]];

    def computeRoot = grow //will be the name of this. if we print this in class Grow
  }.compile(hexagon)
}*/



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






