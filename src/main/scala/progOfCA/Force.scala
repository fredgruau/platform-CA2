package progOfCA

import compiler.ASTL._
import compiler.ASTLfun._
import compiler.SpatialType._
import compiler.{B, V}
import dataStruc.Named
import progOfmacros.RedT.clock2
import progOfmacros.Util.randN12

/** a force is exerted on a support and generates a movement */
abstract class Force {
  /**
   *
   * @param is support on which to apply the force
   * @param r  random BoolV
   * @return
   */
  def action(is: BoolV, r: Rand): CenteredMove
}

/**
 * CenteredMove(=move is defined within the body support
 *
 * @param empty where to withdraw at
 * @param push  where to extends towards
 */
class CenteredMove(val empty: BoolV, val push: BoolVe) extends Named

object Force {
  /** this force is random, but it does break the quasipoint property, eliminating the need for checking gate-expensive mutex
   * as we will do, we use is, in order to localize the force on the agents */
  val qpointRandomForce: Force = new Force {
    override def action(is: BoolV, ra: Rand): CenteredMove = {
      val isqp = is.asInstanceOf[BoolV with QuasiPtify] //this force works only on quasiPoint
      val extend12dir = e(isqp.singleton) & ra.randDir //isolated point move toward one of the 12 possible directions
      val extend2side = clock2(transfer(sym(v(isqp.doubleton) & ra.randSide)))
      new CenteredMove(fromBool[V](false), extend2side | extend12dir)
    }
  }
}