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
import progOfmacros.Comm.{apexE, apexV, neighborsSym, symEv}
import sdn.MovableAgentV
import progOfmacros.Topo
import progOfmacros.Compute._
import progOfmacros.Wrapper.{borderS, exist, existS, inside, insideS, shrink}
import progOfmacros.RedT.{cac, cac2, enlargeEF, enlargeFE, enlargeOld}
import progOfmacros.Topo.{brdin, nbcc, nbccV, nbccVe}


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

/** mixin declaring  brdVe so that we can compute brdE just by adding another  mixin and then BrdV just by reusing an already declared mixin*/
trait HasBrdVeAndE{ val brdVe: BoolVe
  /** we use delayedL because upon creation, brdVe turns out to be not yet constructed */
  val lateBrdVe:BoolVe=delayedL(brdVe)
  val BrdE:BoolE
}



/** mixin adding a brdE to a BrdVe, obsolete, because for one radius is to big,for 2 boolE can be comuted without using the boolVe*/
trait BorderEofVe extends HasBrdVe with HasBrdE {
  //when computing brdE, we need it to be either true or false on the border
  // we can decide to set it to true only if there is a blob, or allways, in which case there will be a center all around the chip,
  // which may be appropriate if we want ports all around the chip. If we want this last behavoir
  // we need to use OR2 instead of OR, where neutral will true instead of false.
  val brdE: BoolE = exist(transfer(lateBrdVe))
}

/** what's needed for blob preservation */
trait Blob {
  val brdE: BoolE
  val brdV: BoolV
  val meetV: BoolV
  val meetE: BoolE
  val nbCc:UintV
   val emptyRhomb:BoolE
  val twoAdjBlob:BoolE
  //we compute a boolV for ease of display
}

trait  BlobConstrain extends Blob  {
  self: MovableAgentV =>
  /** meetV points cannot flip */
  val vmeet = new CancelFlipIf(Both(),meetV,flipOfMove)
  constrain("vmeet",'_',vmeet)
  /**a doubleton cannot flip both vertices*/
  val emeet = new MutKeepFlipIf(Both(),meetE,flipOfMove) with BranchNamed {}
  constrain("emeet",'=',emeet)


}
/** endows  a an agent  defining and edge Frontier (either V or E support) with  its  meeting points.
 * it is reused in BoolV by computing the edge border, and in BoolE by renaming the support as brdE */
trait BlobVouE extends HasBrdE with BorderV with Blob{
  self:HasBrdE =>
  val nbCc: UintV = nbccV(lateBrdE)  //first use of brdE
  val meetV: BoolV = nbCc > 1 //this makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$
  val twoAdjBlob: BoolE = insideS[V, E](brdV) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
  val emptyRhomb: BoolE = ~rhombusExist(lateBrdE) // true if center of a NON-totally empty rhombus
  val meetE: BoolE =  emptyRhomb & twoAdjBlob //two conditions that needs to be met, for meeting edges: empty rhombus and two adjacent blobs.
}

/** endows  a plain BoolV with  its  meeting points. */
trait BlobV extends BorderEofV  with BlobVouE {  self: BoolV => }


/** endows  a  BoolE with  its  meeting points. computes first a borderV */
trait BlobE extends HasBrdE with BlobVouE


trait HasBrdVeEV
/** endows  a  BoolVe COMMING AS THE SLOPELT OF  A DISTANCE with  its  meeting points. using mixin,  computes first a borderE, and then a borderV */
trait BlobVe extends HasBrdVe with BorderV with Blob with Named with BranchNamed {
  val nbCc: UintV = nbccVe(lateBrdVe) //nbcc 's computation is refined compared to BlobV, and BlobE
  val vf: BoolVf = cac(ASTBfun.delta, lateBrdVe)/**  true if all neighbors are at equal distance which happen for a PE is encicled by an hexagon of seeds at distance 2, or a the very begining*/
  // val nicecircle= ~exist(apexV(f(lateBrdE)))
  /**  make sur meetV is on initially, when dg is flat */
  val meetVinit= ~exist(transfer(v(lateBrdE)))
  val meetV: BoolV = ((nbCc > 1)& (nbCc<3))|  meetVinit //makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$1
  val upwardSelle:BoolE =inside(apexE(shrink(lateBrdVe))) //les deux vertex lointaint du losange sont strictement plus loin
  val downwardSelle:BoolE= ~lateBrdE //les deux vertex proches du losange sont a la meme distance
  val selle=upwardSelle&downwardSelle

  val twoAdjBlob: BoolE = insideS[V, E](brdV) //not used for blobVe. attention, pas sur que brdV soit bon cf bug mirror et radius
  val emptyRhomb:BoolE= ~rhombusExist(lateBrdE) //il y a un gros plateau de distance sur tout le rhombus

  val meetE= selle | emptyRhomb //ca n'est pas un vrai gcenter avec emptyrhomb
  }


/**
 *  This class is not necessary anymore using the function addBlobVe we can compute the blob relevant
 *  information for a BoolVe
 * We keep it because it used intelligence to really workout what is needed to be done on the chip border,
 * in the initial case we considered, which was not including mirors.
 * @param brdE  frontier,
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






