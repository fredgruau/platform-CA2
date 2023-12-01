package progOfCA

import compiler.AST.Layer
import compiler.ASTL._
import compiler.ASTLfun.{orR, toNeighb}
import compiler.SpatialType.BoolV
import compiler.{AST, B, V}
import progOfCA.Force.qpointRandomForce

/** we test simple movements */
class Mv() extends Layer[(V, B)](1, "global") with BoolV with Blobify with QuasiPtify {
  val ra = new Rand()
  val m: CenteredMove = qpointRandomForce.action(this, ra)
  val invade = orR(toNeighb(m.push))
  show(this, b.meet, b.nbCc, invade, doubleton, singleton, m.push) // brd,emptyRhomb1, emptyRhomb,twoAdjBlob,
  override val next: AST[(V, B)] = this | (brdV & ~b.meet & invade) //we extend the blob around the border brdV, except for meeting meeting points
}


