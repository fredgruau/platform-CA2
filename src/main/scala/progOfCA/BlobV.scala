package progOfCA

import compiler.AST.Layer
import compiler.ASTLfun._
import compiler.ASTL._
import compiler.SpatialType._
import compiler.Circuit.hexagon
import compiler._
import progOfmacros.BlobMacro._
import progOfmacros.Comm
import progOfmacros.Compute._
import progOfmacros.RedS.{exist, frontier}

/** computes  V-meeting points and E-meeting points in the case of a brave simple BoolV  Blob  */
trait BlobV extends BoolV { //the blob is not necessarily a layer
  self: BoolV =>
  val brd: BoolE = frontier(this)
  // val borderE:BoolE= xorR(transfer(e(this))) //pour tester le calcul du rayon
  val nbCh: UintV = nbccBis(Comm.apexV(f(brd))) //first use of brdE
  // val nbCh: UintV =nbcc(Comm.apexV(f(brdE))) //first use of brdE
  val meetV: BoolV = nbCh > 1 //makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$1
  val emptyRhomb: BoolE = ~exist[F, E](exist[E, F](brd)) //second use of brdE, check that there is a totally empty rhombus between two blobs
  val twoAdjBlob: BoolE = exist[V, E](exist[E, V](brd)) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
  val meetE: BoolE = emptyRhomb & twoAdjBlob //we've got to be able to not have to write calls to andE!!


}

/** uses the blob to grow voronoi region stoping the growth just before merge happens */
class GrowVor() extends Layer[(V, B)](1, "global") with ASTLt[V, B] with BlobV {
  val next: BoolV = orR(neighbors(this)) & (~meetV) & (~exist[E, V](meetE)) //only radius 0 computation, because communication is handled in macro
  show(this, meetE, meetV)
}