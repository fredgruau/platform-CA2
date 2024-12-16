package sdn

// Contains code use to compute fields for maintaining blobs and quasiPoints
// We isolate functionality which can be reused elsewhere such as borderE, borderV.
// We will distinguish basic blobV, EblobE, blobVe. They each requires increasingly complex computation
// blobV could be computed from blobE, which could be computed from BlobEv,
// but we prefer to compute them each one in a specfic way because it is more clear and also more perfomrant.

import compiler.AST.{Call1, Call2, Fundef1, Fundef2, Layer, pL}
import compiler.ASTLfun._
import compiler.ASTL._
import compiler.SpatialType._
import compiler.Circuit.hexagon
import compiler._
import compiler.ASTLt.ConstLayer
import dataStruc.{BranchNamed, Named}
import sdn.MovableAgentV
import progOfmacros.Topo
import progOfmacros.Compute._
import progOfmacros.Wrapper.{borderS, exist, existS, insideS}
import progOfmacros.RedT.{enlargeEF, enlargeFE, enlargeOld}
import progOfmacros.Topo.{brdin, nbcc, nbccV}


/** mixing declaring  brdE so that we can compute brdV just by adding another mixin */
trait HasBrdE{
  val brdE: BoolE
  /** we use delayedL because upon creation, brdE turns out to be not yet constructed */
  val lateBrdE:BoolE=delayedL(brdE)
}

/** Mixing adding a BrdV when BrdE is defined. BrdV contains both inside and outside vertices*/
trait BorderV extends HasBrdE {
  val brdV:BoolV=existS(lateBrdE)
}

/** Mixing adding a brdE representing an edge border of a plain blobV, (obtained with the xor on edge) */
trait BorderEofV extends HasBrdE { self: BoolV =>   val brdE: BoolE = borderS(this)}

/** mixin declaring  brdVe so that we can compute brdE just by adding another  mixin and then BrdV just by reusing an already declared mixin*/
trait HasBrdVe{ val brdVe: BoolVe
  /** we use delayedL because upon creation, brdVe turns out to be not yet constructed */
  val lateBrdVe:BoolVe=delayedL(brdVe)
}

/** mixin adding a brdE to a BrdVe */
trait BorderEofVe extends HasBrdVe with HasBrdE {
  val brdE: BoolE = exist(transfer(lateBrdVe))
}

/** what's needed for blob preservation */
trait Blob {
  val brdE: BoolE
  val brdV: BoolV
  val meetV: BoolV
  val meetE: BoolE
}

trait  BlobConstrain extends Blob  {
  self: MovableAgentV =>
  /** meetV points cannot flip */
  val vmeet = new CancelFlipIf(Both(),meetV)
  constrain("vmeet",vmeet)
  /**a doubleton cannot flip both vertices*/
  val emeet = new MutKeepFlipIf(Both(),meetE) with BranchNamed {}
  constrain("emeet",emeet)


}
/** endows  a an agent  defining and edge Frontier (either V or E support) with  its  meeting points.
 * it is reused in BoolV by computing the edge border, and in BoolE by renaming the support as brdE */
trait BlobVouE extends HasBrdE with BorderV with Blob{
  self:HasBrdE =>
  val nbCc: UintV = nbccV(lateBrdE)  //first use of brdE
  val meetV: BoolV = nbCc > 1 //this makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$1
  val twoAdjBlob: BoolE = insideS[V, E](brdV) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
  val nonEmptyRhomb: BoolE = rhombusExist(lateBrdE) // true if center of a NON-totally empty rhombus
  val meetE: BoolE =  ~nonEmptyRhomb & twoAdjBlob //two conditions that needs to be met, for meeting edges: empty rhombus and two adjacent blobs.
}

/** endows  a plain BoolV with  its  meeting points. */
trait BlobV extends BorderEofV  with BlobVouE {  self: BoolV => }


/** endows  a  BoolE with  its  meeting points. computes first a borderV */
trait BlobE extends HasBrdE with BlobVouE

/** endows  a  BoolVe with  its  meeting points. using mixin,  computes first a borderE, and then a borderV*/
trait BlobVe extends HasBrdVe with BorderEofVe with BorderV with Blob {
  val nbCc: UintV = nbcc(lateBrdVe) //nbcc 's computation is refined compared to BlobV, and BlobE
  val meetV: BoolV = nbCc > 1 //makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$1
  val twoAdjBlob: BoolE = insideS[V, E](brdV) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
  val nonEmptyRhomb: BoolE = rhombusExist(brdE) // true if center of a NON-totally empty rhombus
  /** this is also refined in comparison to BoolV, and BoolE, so as to be able to detect edge gabriel centers, which can also defined as meeting poins */
  val nonEmptyRhomb2: BoolE = orR(transfer(enlargeFE(enlargeEF(lateBrdVe)))) //todo utiliser redT avec un wrapper a la place de enlargeFE, pour faire ca faut utiliser BlobVe POUR DE VRAI
  val meetE: BoolE = ~nonEmptyRhomb2 & twoAdjBlob //two conditions that needs to be met, for edge meeting points
  /*val nbCc: UintV = nbccV(lateBrdE)  //first use of brdE, we use delayedL because upon creation, brdE is not yet available
  val meetV: BoolV = nbCc > 1 //this makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$1
  val twoAdjBlob: BoolE = insideS[V, E](brdV) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
  val nonEmptyRhomb: BoolE = rhombusExist(lateBrdE) // true if center of a NON-totally empty rhombus
  val meetE: BoolE =  ~nonEmptyRhomb & twoAdjBlob //two conditions that needs to be met, for meeting edges: empty rhombus and two adjacent blobs.*/
}




/**
 *
 * @param brdE   frontier,
 * @param brdIn oriented contour, brd is computed from brdIn
 * @param brdV  on the frontier, brdV is computed from brd.
 *              computes  V-meeting points and E-meeting points, plus
 *              memorizes intermediate result, such as nbcc, for later use. */
class BlobOld(brdE: BoolE, brdIn: BoolVe, brdV: BoolV) extends Named with BranchNamed { //the blob is not necessarily a layer todo should be replaced using blobVe
  val nbCc: UintV = nbcc(brdIn) //first use of brdE
  val meetV: BoolV = nbCc > 1 //makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$1
  val twoAdjBlob: BoolE = insideS[V, E](brdV) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
  val nonEmptyRhomb: BoolE = rhombusExist(brdE) // true if center of a NON-totally empty rhombus
  val nonEmptyRhomb2: BoolE = orR(transfer(enlargeFE(enlargeEF(brdIn)))) //more precise computation  for detecting edge gabriel centers,
  // which can also defined as meeting poins
  val meetE: BoolE = {
    ~nonEmptyRhomb2 & twoAdjBlob //two conditions that needs to be met, for edge meeting points
  } //we've got to be able to not have to write calls to andE!!
  val meetEside = existS[E, V](meetE)
  val meet = meetV | meetEside
}


/*//todo a virer
trait QPointify {
  self: BoolV => //quasiPoints are blobs.
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

}*/





