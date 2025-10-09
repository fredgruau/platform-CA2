package sdntool

import compiler.ASTL.transfer
import compiler.ASTLfun.rhombusExist
import compiler.SpatialType.{BoolE, BoolV, BoolVe, BoolVf, UintV}
import compiler.{ASTBfun, E, V}
import dataStruc.{BranchNamed, Named}
import progOfmacros.Topo.{nbccV, nbccVe}
import progOfmacros.Wrapper.{exist, inside, insideS, shrink}
import sdn.{BlobVFields, newBlob}
import compiler.ASTLfun._
import progOfmacros.Comm.apexE
import progOfmacros.RedT.cac

/** contains fields for display and constraint */
class Bloob (val nbCC:UintV,val meetE:BoolE) extends Named with BranchNamed {
  val meetV=nbCC>1  //toujours valable
  /** for V blob, the computation of meeting points uses brdE and brdV */
  def this(f: BlobVFields) = this(nbccV(f.brdE) ,  insideS[V, E](f.brdV)& ~rhombusExist(f.brdE))
  /** for Ve blob, the computation of meeting points uses borderVe */
  //def this(brdE:BoolE,brdVe:BoolVe) = this(nbccVe(brdVe),)

  /*  val meetV: BoolV = nbCc  //this makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$
    val twoAdjBlob: BoolE = insideS[V, E](f.brdV) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
    val emptyRhomb: BoolE = ~rhombusExist(f.brdE) // true if center of a NON-totally empty rhombus
    val meetE: BoolE = emptyRhomb & twoAdjBlob //two conditions that needs to be met, for meeting edges: empty rhombus and two adjacent blobs.

    new Bloob

}*/
}

/*

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
*/



/*
object Bloob{
  def apply(f:FeatureBlobV)= new Bloob with Named with BranchNamed {
      val nbCc: UintV = nbccVe(f.brdVe)
      val meetV: BoolV = nbCc > 1 //this makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$
      val twoAdjBlob: BoolE = insideS[V, E](f.brdV) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
      val emptyRhomb: BoolE = ~rhombusExist(f.brdE) // true if center of a NON-totally empty rhombus
      val meetE: BoolE = emptyRhomb & twoAdjBlob //two conditions that needs to be met, for meeting edges: empty rhombus and two adjacent blobs.
    }


  }


}*/

