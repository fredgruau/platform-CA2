package progOfCA

import compiler.ASTLfun.{e, fromBool}
import compiler.SpatialType._
import compiler.{B, V}
import dataStruc.Named
import progOfmacros.Util.randN12

abstract class Force {

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
  /** this force is random, but it does break the quasipoint property, eliminating the need for checking gate-expensive mutex */
  val qpointRandomForce: Force = new Force {
    override def action(is: BoolV, ra: Rand): CenteredMove = {
      val isqp = is.asInstanceOf[BoolV with QuasiPtify] //this force works only on quasiPoint
      val directionalExtend = e(isqp.singleton) & ra.randEdge //isolated point move toward one of the 12 possible directions
      new CenteredMove(fromBool[V](false), directionalExtend)
    }
  }
}