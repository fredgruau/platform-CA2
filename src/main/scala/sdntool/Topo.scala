package sdn

/*
// Contains code use to compute fields for maintaining blobs and quasiPoints
// We isolate functionality which can be reused elsewhere such as borderE, borderV.
// We will distinguish basic blobV, blobE, blobVe. They each requires increasingly complex computation
// blobV could be computed from blobE, which could be computed from BlobEv,
// but we prefer to compute them each one in a specfic way because it is more clear and also more perfomrant.
*/

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
import progOfmacros.RedT.{cac, enlarge, enlargeEF, enlargeFE}
import progOfmacros.Topo.{brdin, nbcc, nbccV, nbccVe}
import sdn.Util.addSym
import sdntool.{Bloob, addDist}
/** contains fields that can be computed for any boolV representing blobs, not just Vagents
 * for exemple, we can us it to grow voronoi, which needs meeting point
 * */
class BlobVFields(val muis:BoolV with carrySysInstr) extends Attributs {
  /** true on the border of the blob */
  val brdE:BoolE=  borderS(~(~ muis) )//push everywhere possible. todo enlever la double négation.
  /** true on vertices next to the border of the blob */
  val  brdV:BoolV=existS(brdE)
  val isVe:BoolVe=e(muis)
  val notVe= ~isVe
  /** Ve edges leaving the support , we know we may take a sym so we prepare for it, to get a meaningfull name brdVe.sym*/
  val brdVe=transfer(v(brdE)) & isVe//addSym introduit un delayed et compromet le nommage automatique par reflection. addSym( transfer(v(brdE)) & isVe)
  override def showMe={ shoow(brdE,brdV,brdVe)   }
}
/** endows a movableAgentV with the feature needed to a blob stored in a class "f" (shortname) */
trait addBlobVfields{ self: MovableAgentV =>
  val bf=new BlobVFields(muis)
}

trait blob {val meetV:BoolV; val meetE:BoolE}

/** declares a bunch of spatial attributes, provide the trait to show some of them */
abstract class Attributs extends  hasMuisSysInstr with shoow with BranchNamed with Named{
  def showMe
}

/** fields common to all blobs properties; */
abstract class Blob extends Attributs {  val meetV:BoolV; val meetE:BoolE; val nbCc:UintV
  /** allows to picture meeE as vertices */
  def meetE2=existS[E,V](meetE)
  /** regroup all meeting points and so, all gabriel centers */
  val meet= ~ (~ delayedL(meetV | meetE2)) //double négation nécessaire pour nommer.
override def showMe=shoow(meetV,meetE,nbCc,meet)}

/**
 *
 * @param muis allows to shoow
 * @param f generic fields of a blob, needed to compute meeting points
 */
class BlobV(val muis:BoolV with carrySysInstr,f:BlobVFields) extends Blob  {
  val nbCc=nbccV(f.brdE)
  val meetV=nbCc>1
  val twoAdjBlob: BoolE = insideS[V, E](f.brdV) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
  val emptyRhomb: BoolE = ~rhombusExist(f.brdE) // true if center of a NON-totally empty rhombus
  val meetE=twoAdjBlob & emptyRhomb
  /** */
  override  def showMe={super.showMe;shoow(twoAdjBlob,emptyRhomb) }
}

/** endows a movableAgentV with the blob meeting points */
trait addBloobV{ self: MovableAgentV with addBlobVfields =>val b=new BlobV(muis,bf)}
/** endows  a  BoolVe COMMING AS THE SLOPELT OF  A DISTANCE with  its  meeting points
 * those meeting points correspond to the gabriel centers.
 * It computes first a borderE, */
class BlobVe(val muis:BoolV with carrySysInstr,brdE:BoolE, brdVe:BoolVe) extends Blob{
  val nbCc: UintV = nbccVe(brdVe) //nbcc 's computation is refined compared to BlobV, and BlobE
  val vf: BoolVf = cac(ASTBfun.delta, brdVe)/**  true if all neighbors are at equal distance which happen for a PE is encicled by an hexagon of seeds at distance 2, or a the very begining*/
  /**  make sur meetV is on initially, when dg is flat */
  val meetVinit= ~exist(transfer(v(brdE))) //todo, si ca se trouve ca coresponds a nbcc==0 qui serai plus esthetique
  val meetV: BoolV = ((nbCc > 1)& (nbCc<3))|  meetVinit //makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$1
  val upwardSelle:BoolE =inside(apexE(shrink(brdVe))) //les deux vertex lointaint du losange sont strictement plus loin
  val downwardSelle:BoolE= ~brdE //les deux vertex proches du losange sont a la meme distance
  val selle=upwardSelle&downwardSelle
   val emptyRhomb:BoolE= ~rhombusExist(brdE) //il y a un gros plateau de distance sur tout le rhombus
  val meetE= selle | emptyRhomb //ca n'est pas un vrai gcenter avec emptyrhomb

  override def showMe: Unit = {super.showMe;shoow(emptyRhomb);shoow(meetE2)}
}

/** endows a distance with BlobVE meeting points, which are Gcenter */
trait addBloobVe{ self: MovableAgentV with addBlobVfields with addDist=>val b=new BlobVe(muis,d.voisinDiff,  d.sloplt)}
/** endows a distance with Gcenter which are almost the same as BlobV'
 * gabriel centers can be directly obtain simply by computing Vmeeting-point of the blob, using sloplt
 *  and also Emeeting points, nearest to the source.
 * */
trait addGcenter{ self: MovableAgentV with addBlobVfields with addDist=>
  val gc=new BlobVe(muis,d.voisinDiff,  d.sloplt){
    /** silly way of avoiding superposition of agents with Gcenter, we use a val for testing */
    override val meetE2: ASTLt[V, B] = super.meetE2 & ~ muis}} //todo verifier que override fonctionne





/** declares  brdE so that we can compute brdV just by adding another mixin */
trait HasBrdE{
  val brdE: BoolE
  /** we use delayedL because upon creation, brdE turns out to be not yet constructed */
  val lateBrdE:BoolE=delayedL(brdE)
}

/** Mixing adding a BrdV when BrdE is defined. BrdV contains both inside and outside vertices*/
trait BorderV extends HasBrdE {
  val brdV:BoolV=existS(lateBrdE)
}

trait newBrdVT extends HasBrdE {
  val newbrdV:BoolV=existS(lateBrdE)
}

/** adds a brdE representing an edge border of a plain blobV, (obtained with the xor on edge) */
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

/** deefines computation needed for preserving conncectedness of blobs */
/*trait Blob {
  val brdE: BoolE
  val brdV: BoolV
  val meetV: BoolV
  val meetE: BoolE
  val nbCc:UintV
   val emptyRhomb:BoolE
  val twoAdjBlob:BoolE
  //we compute a boolV for ease of display
}*/
trait newBlob {
  val meetV: BoolV
  val meetE: BoolE
  val nbCc:UintV
  val emptyRhomb:BoolE
  val twoAdjBlob:BoolE
  //we compute a boolV for ease of display
}
/*

trait  BlobConstrain extends Blob  {
  self: MovableAgentV =>
  /** meetV points cannot flip */
  val vmeet = new CancelFlipIf(Both(),meetV,flipOfMove)
  constrain("vmeet",'_',vmeet)
  /**a doubleton cannot flip both vertices*/
  val emeet = new MutKeepFlipIf(Both(),meetE,flipOfMove) with BranchNamed {}
  constrain("emeet",'=',emeet)
}
*/

trait  newBlobConstrain   {
  self: MovableAgentV with addBloobV=>
  /** meetV points cannot flip */
  val vmeet = new CancelFlipIf(Both(),b.meetV,flipOfMove)
  constrain("vmeet",'_',vmeet)
  /**a doubleton cannot flip both vertices*/
  val emeet = new MutKeepFlipIf(Both(),b.meetE,flipOfMove) with BranchNamed {}
  constrain("emeet",'=',emeet)
}
/** endows  a an agent  defining and edge Frontier (either a BoolV agent or E support) with  its  meeting points.
 * it is reused in BoolV by computing the edge border, and in BoolE by renaming the support as brdE */
trait newBlobVouE extends UtilVagent{
  self:MovableAgentV =>
  /** put all the info an anonymous attribute called "b", for hierarchical ordering of info, and printing */
  val newb = new newBlob with Named with BranchNamed {
    val nbCc: UintV = nbccV(laateBrdE) //first use of brdE
    val meetV: BoolV = nbCc > 1 //this makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$
    val twoAdjBlob: BoolE = insideS[V, E](newbrdV) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
    val emptyRhomb: BoolE = ~rhombusExist(laateBrdE) // true if center of a NON-totally empty rhombus
    val meetE: BoolE = emptyRhomb & twoAdjBlob //two conditions that needs to be met, for meeting edges: empty rhombus and two adjacent blobs.
    def showMe={ shoow(nbCc,meetV,twoAdjBlob,emptyRhomb,meetE,laateBrdE)}
  }
}


/*
trait BlobVouE extends HasBrdE with BorderV with Blob{
  self:HasBrdE =>
  val nbCc: UintV = nbccV(lateBrdE)  //first use of brdE
  val meetV: BoolV = nbCc > 1 //this makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$
  val twoAdjBlob: BoolE = insideS[V, E](brdV) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
  val emptyRhomb: BoolE = ~rhombusExist(lateBrdE) // true if center of a NON-totally empty rhombus
  val meetE: BoolE =  emptyRhomb & twoAdjBlob //two conditions that needs to be met, for meeting edges: empty rhombus and two adjacent blobs.
}
*/

/** endows  a plain BoolV with  its  meeting points. */
//trait BlobV extends BorderEofV  with BlobVouE {  self: BoolV => }

/** endows  a  BoolE with  its  meeting points. computes first a borderV */
//trait BlobE extends HasBrdE with BlobVouE
/** endows  a  BoolE with  its  meeting points. computes first a borderV */

//trait newBlobE extends HasBrdE with newBlobVouE
//trait HasBrdVeEV
/*

/** endows  a  BoolVe COMMING AS THE SLOPELT OF  A DISTANCE with  its  meeting points
 * those meeting points correspond to the gabriel centers.
 * It computes first a borderE, and then a borderV using mixing*/
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

*/

/** endows  a  BoolVe COMMING AS THE SLOPELT OF  A DISTANCE with  its  meeting points
 * those meeting points correspond to the gabriel centers.
 * It computes first a borderE, and then a borderV using mixing*/
trait newBlobVe extends HasBrdVe with newBrdVT with newBlob with Named with BranchNamed {
  val nbCc: UintV = nbccVe(lateBrdVe) //nbcc 's computation is refined compared to BlobV, and BlobE
  val vf: BoolVf = cac(ASTBfun.delta, lateBrdVe)/**  true if all neighbors are at equal distance which happen for a PE is encicled by an hexagon of seeds at distance 2, or a the very begining*/
  // val nicecircle= ~exist(apexV(f(lateBrdE)))
  /**  make sur meetV is on initially, when dg is flat */
  val meetVinit= ~exist(transfer(v(lateBrdE)))
  val meetV: BoolV = ((nbCc > 1)& (nbCc<3))|  meetVinit //makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$1
  val upwardSelle:BoolE =inside(apexE(shrink(lateBrdVe))) //les deux vertex lointaint du losange sont strictement plus loin
  val downwardSelle:BoolE= ~lateBrdE //les deux vertex proches du losange sont a la meme distance
  val selle=upwardSelle&downwardSelle
  val twoAdjBlob: BoolE = insideS[V, E](newbrdV) //not used for blobVe. attention, pas sur que brdV soit bon cf bug mirror et radius
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






