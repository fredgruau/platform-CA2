package progOfCA

import compiler.ASTL._
import compiler.ASTLfun._
import compiler.SpatialType._
import compiler.{ASTLt, B, E, T, V}
import dataStruc.Named
import progOfmacros.RedT.clock2
import progOfmacros.Util.randN12
import simulator.Util.show

/** a force is exerted on a support and generates a movement */
abstract class Force extends  Named {
  /**
   *
   * @param is support on which to apply the force
   * @param r  random BoolV
   * @return an agent-centered move
   */
  def action(is: BoolV): MoveC
}

/** adds the possibility of using a randomizer */
trait rando{val r = new Rand()
}

/**
 * MoveC is a centered move is a move defined within the body support
 *
 * @param empty where to withdraw at
 * @param push  where to extends towards
 */
class MoveC(val empty: BoolV, val push: BoolVe) extends Named

/** defines classic forces */
object Force {
  /** this force is random, but it does break the quasipoint property,
   * eliminating the need for checking gate-expensive mutex
   * when applied, the movement produced is already centered on the agents.
   * However, we must still check for directionnality using
   * sophisticated blob tests, because combination with other force may break directionality */
  val qpointRand: Force = new Force() with rando  {
    override def action(is: BoolV): MoveC = {
      val isqp = is.asInstanceOf[BoolV with QPointify] //this force works only on quasiPoint
      val extend12dir: BoolVe = e(isqp.singleton) & r.randDir //isolated point move toward one of the 12 possible directions
      val extend2side: BoolVe = clock2(transfer(sym(v(isqp.doubleton) & r.randSide)))
      new MoveC(fromBool[V](false), extend2side | extend12dir) //ici on fait un or sur des boolVe
    }
  }

}