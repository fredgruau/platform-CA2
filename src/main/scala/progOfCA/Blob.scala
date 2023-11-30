package progOfCA

import compiler.AST.{Call1, Call2, Fundef1, Fundef2, Layer, pL}
import compiler.ASTLfun._
import compiler.ASTL._
import compiler.SpatialType._
import compiler.Circuit.hexagon
import compiler._
import compiler.ASTLt.ConstLayer
import dataStruc.Named
import progOfmacros.Topo
import progOfmacros.Compute._
import progOfmacros.RedSwrapper.{border, exist, inside}
import progOfmacros.Topo.{brdin, nbcc}

/** endows a V-body with the blob meeting points. */
trait Blobify {
  self: BoolV =>
  val brd: BoolE = border(this)
  val brdIn: BoolVe = brdin(brd, this)
  val brdV = orR(brdIn)
  val b = new Blob(border(this), brdIn, orR(brdIn))
}

/**
 *
 * @param brd   frontier,
 * @param brdIn oriented contour, brd is computed from brdIn
 * @param brdV  on the frontier, brdV is computed from brd.
 *              computes  V-meeting points and E-meeting points, plus
 *              memorizes intermediate result, such as nbcc, that be usedlater. */
class Blob(brd: BoolE, brdIn: BoolVe, brdV: BoolV) extends Named { //the blob is not necessarily a layer
  val nbCc: UintV = nbcc(brdIn) //first use of brdE
  val meetV: BoolV = nbCc > 1 //makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$1
  val nonEmptyRhomb: BoolE = rhombusExist(brd) // true if center of a totally empty rhombus
  val twoAdjBlob: BoolE = inside[V, E](brdV) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
  val meetE: BoolE = ~nonEmptyRhomb & twoAdjBlob //we've got to be able to not have to write calls to andE!!
  val meetEside = exist[E, V](meetE)
  val meet = meetV | meetEside

}

trait QuasiPtify {
  self: BoolV with Blobify => //quasiPoints are blobs.
  val doubleton: BoolE = inside[V, E](this)
  val singleton: BoolV = inside[E, V](doubleton)
  val tripleton: BoolF = inside[V, F](this)

}

class Quasipoint(is: BoolV) extends Named {
  val doubleton: BoolE = inside(is)

}





