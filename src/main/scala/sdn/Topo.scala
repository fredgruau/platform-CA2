package progOfCA

import compiler.AST.{Call1, Call2, Fundef1, Fundef2, Layer, pL}
import compiler.ASTLfun._
import compiler.ASTL._
import compiler.SpatialType._
import compiler.Circuit.hexagon
import compiler._
import compiler.ASTLt.ConstLayer
import dataStruc.{BranchNamed, Named}
import progOfmacros.Topo
import progOfmacros.Compute._
import progOfmacros.Wrapper.{borderS, existS, insideS}
import progOfmacros.RedT.{enlarge, enlargeEF, enlargeFE}
import progOfmacros.Topo.{brdin, nbcc}

/* *
Contains code use to compute fields for maintaining topological invariant such as blobs, and quasipoints
 */


/** endows a V-body with the blob meeting points. */
trait Blobify {
  self: BoolV =>
  val brd: BoolE = borderS(this)
  val brdIn: BoolVe = brdin(brd, this)
  val brdV = orR(brdIn)
  val b = new Blob(borderS(this), brdIn, orR(brdIn))
}

/**
 *
 * @param brd   frontier,
 * @param brdIn oriented contour, brd is computed from brdIn
 * @param brdV  on the frontier, brdV is computed from brd.
 *              computes  V-meeting points and E-meeting points, plus
 *              memorizes intermediate result, such as nbcc, for later use. */
class Blob(brd: BoolE, brdIn: BoolVe, brdV: BoolV) extends Named with BranchNamed { //the blob is not necessarily a layer
  val nbCc: UintV = nbcc(brdIn) //first use of brdE
  val meetV: BoolV = nbCc > 1 //makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$1
  val twoAdjBlob: BoolE = insideS[V, E](brdV) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
  val nonEmptyRhomb: BoolE = rhombusExist(brd) // true if center of a NON-totally empty rhombus
  val nonEmptyRhomb2: BoolE = orR(transfer(enlargeFE(enlargeEF(brdIn)))) //more precise computation  for detecting edge gabriel centers,
  // which can also defined as meeting poins
  val meetE: BoolE = {
    ~nonEmptyRhomb2 & twoAdjBlob //two conditions that needs to be met, for edge meeting points
  } //we've got to be able to not have to write calls to andE!!
  val meetEside = existS[E, V](meetE)
  val meet = meetV | meetEside

}

trait QPointify {
  self: BoolV with Blobify => //quasiPoints are blobs.
  /** true for the vertices of a qpt consiting exactly of one vertices */
  val singleton: BoolV = andR(neighbors(~this)) & this
  /** true if both apex vertices of the edge are empty */
  val bothApexEmpty: BoolE = ~orR(apex[V, E, B](f(this)))
  /** true for the edge inside qpt consiting exactly of two vertices */
  val doubleton: BoolE = insideS[V, E](this) & bothApexEmpty
  /** true for the face inside a qpt consiting exactly of three adjacent  vertices */
  val tripleton: BoolF = insideS[V, F](this)
  val q = new QuasiPoint(this)
}

class QuasiPoint(is: BoolV) extends Named {

}





