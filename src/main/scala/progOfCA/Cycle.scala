package progOfCA

import compiler.SpatialType._
import compiler.AST.{Layer, _}
import compiler.ASTLfun.inc
import compiler.SpatialType._
import compiler.{AST, ASTLt, B, SI, UI, V, repr}
import progOfmacros.RedS.leastUI
import simulator.Util.show

/** produce a global uniform field cycling through the 2^nbit values, that can be used for testing */
class Cycle() extends Layer[(V, UI)](3, "random") with UintV {
  override val next: UintV = inc(this);
  //val nouv:IntV = this + maxSI()
  //val nouv:IntV=min(this,0)
  //show (nouv)
  show(this)
}

/** used  to test add and then automatic generation of maxSI on 4 bits which is 3 encoded as  011 */
class Cyclep() extends Layer[(V, UI)](3, "random") with UintV {
  val leastE: UintE = leastUI(this)
  val leastV: UintV = leastUI(leastE)
  override val next: UintV = leastV //inc(this)
  show(this)
  show(leastE)
  show(leastV)
}

class CyclepOld1() extends Layer[(V, UI)](3, "random") with UintV {
  val leastE: UintE = leastUI(this)
  val leastV: UintV = leastUI(leastE)
  override val next: UintV = leastV //inc(this)
  show(this)
  show(leastE)
  show(leastV)
}

/*
class CycleMin3() extends Cycle {
  val min3 = min ( this, 3)
  show(min3);
}*/
