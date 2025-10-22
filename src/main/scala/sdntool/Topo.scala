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
import progOfLayer.Sextexrect.chooseMaxOf
import progOfStaticAgent.Convergent
import progOfmacros.Comm.{apexE, apexV, insideBall, neighborsSym, symEv}
import sdn.MovableAgV
import progOfmacros.{Topo, Wrapper}
import progOfmacros.Compute._
import progOfmacros.Wrapper.{borderS, exist, existS, inside, insideS, not, shrink, shrink1, shrink2, shrink3}
import progOfmacros.RedT.{cac, enlarge, enlargeEF, enlargeFE}
import progOfmacros.Topo.{brdin, nbcc, nbccV, nbccVe}
import sdn.Globals.root4naming
import sdn.Util.addSym
import sdntool.{MuDist, addDist}
/** contains fields that can be computed for any boolV representing blobs, not just Vagents
 * for exemple, we can us it to grow voronoi, which needs meeting point
 * */

/** declares a bunch of spatial attributes, provide the necessary trait "show"  to show a selection of them */
abstract class Attributs extends  hasMuisSysInstr with shoow with BranchNamed with Named{
  def showMe
}

class BlobVFields(val muis:BoolV with carrySysInstr) extends Attributs {
  /** true on the border of the blob */
  val brdE:BoolE=  borderS(~(~ muis) )//push everywhere possible. todo enlever la double négation.
  /** true on vertices next to the border of the blob */
  val  brdV:BoolV=existS(brdE)
  val isVe:BoolVe=e(muis)
  /** true if there is filled vertice toward each of the 6 directions */
  val qqnEnFace:BoolVe=neighborsSym(isVe)
  val notVe= ~isVe
  /** Ve edges leaving the support , we know we may take a sym so we prepare for it, to get a meaningfull name brdVe.sym*/
  val brdVeIn=transfer(v(brdE)) & isVe//addSym introduit un delayed et compromet le nommage automatique par reflection. addSym( transfer(v(brdE)) & isVe)
  val brdVeOut=transfer(v(brdE)) & e(~muis)//todo bien possible qu'on puisse travailler juste avec un seul brdVe
  val rand= root4naming.addRandBit().asInstanceOf[BoolV]
  val lightConcave=( exist(shrink3(brdVeOut)) | (exist(shrink2(brdVeOut)) & rand) ) & ~  inside(brdVeOut)

  val smoothen: Force = new Force() {
    override def actionV(ag: MovableAgV): MoveC = {
      /** true if >= three consecutive neighbors & ~  inside(brdVeOut) rules out singleton holes which would otherwise be filled*/


      val inE:BoolE=insideS(muis)
      /**  */
      val convex: BoolV = ~exist(shrink1(transfer(v(inE))))
      val oui= MoveC1(ag.muis & convex, brdVeIn & neighborsSym(e(lightConcave)) )
        oui
    }
  }
  override def showMe={ shoow(brdE,brdV,brdVeIn,brdVeOut)   }
}
/** endows a movableAgentV with the feature needed to a blob stored in a class "f" (shortname) */
trait addBlobVfields{ self: MovableAgV =>
  val bf=new BlobVFields(muis)
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
  override  def showMe={super.showMe;shoow(emptyRhomb) }
}

/** endows a movableAgentV with the blob meeting points */
trait addBloobV{ self: MovableAgV with addBlobVfields =>val b=new BlobV(muis,bf)}
/** endows  a  BoolVe COMMING AS THE SLOPELT OF  A DISTANCE with  its  meeting points
 * those meeting points correspond to the gabriel centers.
 * It computes first a borderE, muis is passed for the sole pupose of enabling shoow */
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

  override def showMe: Unit = {
    super.showMe
    //;shoow(emptyRhomb);shoow(meetE2)
  }
}

/** endows a distance with BlobVE meeting points */
//trait addBloobVe{ self: MovableAgV with addBlobVfields with addDist=>val b=new BlobVe(muis,d.voisinDiff,  d.sloplt)}
/** endows a distance with Gabriel center which are almost the same as BlobVe'
 * gabriel centers can be directly obtain simply by computing Ve-meeting-point  using sloplt
 * we also need brdE
 * */
trait addGcenter{
  self: MovableAgV with addBlobVfields with addDist=>
  val thismuis=muis
  val bve=new BlobVe(muis,d.voisinDiff,  d.sloplt){
    /**  silly way of avoiding superposition of agents with Gcente
     * we just subtract muis from meet2r,
     * we use a val for testing */
    override val meetE2: ASTLt[V, B] = (super.meetE2 )& ~ thismuis}

    val gc= new DetectedAgV(bve.meetE2|bve.meetV) with keepInsideForce {
    override def inputNeighbors = List(d)
  }
} //todo verifier que override fonctionne
trait blobConstrTrou{
  self: MovableAgV with addBloobV=>
  val videPlein= MutKeepFlipIf(Both(),bf.brdE) _ ;  addConstraint("videplein",';',videPlein)}
trait  blobConstrain   {
  self: MovableAgV with addBloobV=>
  /** meetV points cannot flip */
  val vmeet: PartialUI => Constr =  CancelFlipIf(Both(),b.meetV) _
  addConstraint("vmeet",'_',vmeet)
  /**a doubleton cannot flip both vertices*/
  val emeet = MutKeepFlipIf(Both(),b.meetE) _ ;  addConstraint("emeet",'=',emeet);}
/** field needed to compute the constraints of  a quasipoint, and possibly elsewehere */

trait addQpointFields {
  self: MovableAgV with addBlobVfields => //MovableAgentV with addBlobVfields =>
  /** allows to refere to the englobing class from the body of the anonymous attribute */
  private val selfRef = this
  /** on utilise une classe anonyme pour stoquer les fields utiliser pour réaliser un quasipoints */
  val qf = new Attributs() {
    override val muis: BoolV with carrySysInstr = selfRef.muis
    /** true for the vertices of a qpt consiting exactly of one vertices */
    val singleton: BoolV = inside(bf.brdVeIn) & muis
    val nonsingleton = ~singleton & muis
    val next2NonSingleton = exist(neighborsSym(e(nonsingleton)))
    /** true if both apex vertices of the edge are empty */
    val bothApexEmpty: BoolE = not(orR(apex[V, E, B](f(muis))))
    /** true for the edge inside qpt consiting exactly of two vertices */
    val doubleton: BoolE = insideS[V, E](muis) & bothApexEmpty
    val doubletonV: BoolV = existS[E, V](doubleton)
    val isApexV: BoolV = exist[F, V](apexV(f(doubleton)))
    /** true for the face inside a qpt consiting exactly of three adjacent  vertices */
    val tripleton: BoolF = insideS[V, F](muis)
    val tripletonV: BoolV = existS[F, V](tripleton)
    //val choose: BoolVe =chooseMinOf(prio)
    //val choose: BoolVe = chooseMaxOf(prioYesNotQuiescent, 4) //todo deplacer dans constraint ca fait jouer prio
    override def showMe = {
      shoow(doubletonV, tripletonV)
    }
  }
}

/** defines all the constraint that should be met by a quasipoint,
 * nb: constraints must be expressed as function of prio, and flip
 * since we do not know those at the time of constraint creation. */
trait  QpointConstrain extends addQpointFields  with rando {
  self: MovableAgV => //a quasi point  is allways a movableAgentV

  /**
   *
   * @param feature
   * return a boolV true throughout the seed,
   * if and only if feature is also true throughout the seed
   */
  def forallize(feature:BoolV)={
    insideBall(imply(muis, feature))
  }

  /** will choose neighbor with higest flip priority in fp, does not depends on flip  */
  val  sexKeepFlipIf= (fp:PartialUI)=>new Constr(Array(this), null, fp) with Named with BranchNamed {
    /** carefull with the number of bit, 4
     * carefull that this constraint uses prioYesNotQuiescent so it assumes that moves have been already computed
     * if we want to endows our agent with constraints before computing moves, this will not work*/

    val choose: BoolVe = chooseMaxOf(fp.value, 4) //todo deplacer dans constraint ca fait jouer prio
    val whereto:BoolVe= imply(e(qf.singleton),choose)
    /** where = places where flips is still valid after the constraint newFlip<-oldFlip&where
     * defined has a method, in order allow definition prior to intanciation of needed field, such as flip.  */
    override val where: BoolV = inside(neighborsSym(whereto))
  }
  addConstraint("growToTwo",'x',sexKeepFlipIf)
  /** true for neighbors of non singleton*/
  //  val next2NonSingleton = exist(neighborsSym(e(doubletonV | tripletonV)))

  /**  cancel growth for non singleton, exept for doubleton, on appex, this needs a tournament*/
  val leqQuatre =    KeepFlipIf(One(false),implique(qf.next2NonSingleton, qf.isApexV)) _
  addConstraint("leqQuatre",'q',leqQuatre)
  /** singleton cannot flip */
  val diseaperSingle = CancelFlipIf(One(true),qf.singleton)_
  addConstraint("diseaperSingle",'s',diseaperSingle)
  /**a doubleton cannot flip both vertices*/
  val diseaperDouble = MutKeepFlipIf(One(true),qf.doubleton)_
  addConstraint("diseaperDouble",'d',diseaperDouble)
  /** cannot grow from two, to four on both apex */
  val appearDouble = MutApexKeepFlipIf(One(false),qf.doubleton) _
  addConstraint("appearDouble",'a',appearDouble)
  /**  a tripleton cannot flip its three vertices*/
  val diseaperTriple=TriKeepFlipIf(One(true),qf.tripleton)_
  addConstraint("diseaperTriple",'t',diseaperTriple)

  //val extend2side: BoolVe = clock2(transfer(sym(v(doubleton) & rand.randSide)))


  /** used to compute flip cancelation depending on impact */
}





