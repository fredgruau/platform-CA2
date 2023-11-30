package progOfCA

import compiler.ASTLfun.{e, fromBool}
import compiler.SpatialType._
import compiler.{B, V}
import progOfmacros.Util.randN12

abstract class Force {
  def action(is: BoolV): CenteredMove
}

/**
 * move is defined within a boolV area
 *
 * @param empty where to withdraw
 * @param push  where to extends
 */
class CenteredMove(empty: BoolV, push: BoolVe)

object Force {
  /** this force is random, but it does break the quasipoint property, eliminating the need for checking gate-expensive mutex */
  val randomForceQpoint: Force = new Force {
    override def action(is: BoolV with QuasiPtify): CenteredMove = {
      val directionalExtend = e(is & is.singleton) & randN12(is)
      new CenteredMove(fromBool[V](false), directionalExtend)
    }
  }
}