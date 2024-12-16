package progOfCA

import compiler.AST.Layer
import compiler.ASTL._
import compiler.ASTLfun.{orR}
import compiler.SpatialType.BoolV
import compiler.{AST, B, V}
import progOfmacros.Comm.neighborsSym
import progOfmacros.Wrapper.exist

import java.util
import scala.collection.immutable.HashMap

/** we test simple movements */
/*class Mv() extends Layer[(V, B)](1, "global") with BoolV with Blobify with QPointify {
  //all the forces to be applied.
  val forces:util.HashMap[Int,Force]=new util.HashMap[Int,Force]()  //we use a java hashmap in order to recognize if from the java Naming algorithm
 // forces.put(0,qpointRand)
  val m: MoveC = forces.get(0).action(this)
  val invade = exist(neighborsSym(m.push))
  show(this, b.meet, b.nbCc, invade, doubleton, singleton, m.push) // brd,emptyRhomb1, emptyRhomb,twoAdjBlob,
  override val next: AST[(V, B)] = this | (brdV & ~b.meet & invade) //we extend the blob around the border brdV, except for meeting  points
}*/