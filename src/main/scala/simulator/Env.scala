package simulator

import Simulator.CAtype._

/**
 * contains all the information needed to run a given CA.
 *
 * @param ca
 * @param mem Memory of the CA, it is being rewritten by the running thread, but not if being displayed
 * @param time
 * @param randomRoot
 * @param initLayer
 */
class Env(val ca: CAloops, mem: CAmem, val time: Integer, randomRoot: Integer, initLayer: InitLayers) {
  /** true if the CA's current state is being displayed */
  val beingDisplayed: Boolean = false
  /** contains a thread which iterates the CA, while not asked to pause */
  val thread: Thread = null

}
