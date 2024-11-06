package progOfCA //contains variation of grow, illustgrate redS sytematic computation

import compiler.ASTLfun.{neighbors, v}
import compiler.AST.{Layer, pL}
import compiler.SpatialType._
import compiler.ASTL._
import compiler.Circuit.hexagon
import compiler.{AST, ASTBfun, ASTLt, B, Circuit, E, F, T, V}
import progOfmacros.Wrapper.{existS, borderS, insideS}
import compiler.ASTLfun._
import progOfmacros.Topo.brdin


/** uses the blob computation to grow seed into Voronoi region, just by stoping the growth just before merge happens */

class GrowVor() extends Layer[(V, B)](1, "global") with BoolV with Blobify {
  show(this, b.meet) // brd,emptyRhomb1, emptyRhomb,twoAdjBlob,
  override val next: AST[(V, B)] = this | (brdV & ~b.meet) //we extend the blob around the border brdV, except for meeting meeting points
}
/** Simple growth from V to E to V; test of in, and border.we believe that at least for border, and neighbor, it will be reused */
class Grow extends Layer[(V, B)](1, "global") with ASTLt[V, B] {
  val n: BoolE = existS(this);
  // val in: BoolE = inside(this);
  val brd: BoolE = borderS(this);
  override val next: BoolV = existS(n) //   uses  defVe implicitely, the override keyword is mandatory
  show(this, next, n, brd)
  // he name of root to arg(0).lowercase
}

/** Simple growth using directly the neighbor vertice,  that is a bit cheaper */
class GrowN extends Layer[(V, B)](1, "global") with ASTLt[V, B] {
  override val next: BoolV = orR(neighbors(this)) //  make use of defVe brough to us implicitely,
  // nb if overrid is not written, it does not work!
  show(this) //shown field will get the name "grow", because we set the name of root to arg(0).lowercase
  show(next)
}

/** Growing by passing through from V through F */
class GrowF extends Layer[(V, B)](1, "global") with ASTLt[V, B] {
  val nf: BoolF = existS(this); //no use of  defEv
  override val next: BoolV = existS(nf) //  make use of defVf brough to us implicitely,nb if overrid is not written, it does not work!
  show(this, nf, next)

}

/** Growing  from E through F */
class GrowEF extends Layer[(E, B)](1, "global") with ASTLt[E, B] {
  val broadcasted = f(this) //step 1 is broadcast
  val transfered = transfer(broadcasted) //step 2 is transfer
  val nf = orR(transfered) //(n,m,d) yzeté implicit killerest
  override val next: BoolE = existS(nf) //  make use of defVe brough to us implicitely,nb if overrid is not written, it does not work!
  show(this, broadcasted, transfered, nf, next)
}

/** Growing  from E through V */
class GrowEV extends Layer[(E, B)](1, "global") with ASTLt[E, B] {
  val broadcasted = v(this) //step 1 is broadcast
  val transfered = transfer(broadcasted) //step 2 is transfer
  val nv: BoolV = orR(transfered) //(n,m,d) yzeté implicit killerest
  override val next: BoolE = existS(nv) //  make use of defVe brough to us implicitely,nb if overrid is not written, it does not work!
  show(this, broadcasted, transfered, nv, next)
}









