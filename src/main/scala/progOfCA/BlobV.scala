package progOfCA

import compiler.ASTLfun._
import compiler.ASTL._
import compiler.SpatialType._
import compiler.Circuit.hexagon
import compiler._
import progOfmacros.SReduce._
import progOfmacros.BlobMacro._
import progOfmacros.Comm
import progOfmacros.Compute._

/** computes  V-meeting points and E-meeting points in the case of a brave simple BoolV  Blob  */
trait BlobV extends BoolV { //the blob is not necessarily a layer
  self: BoolV =>
  val brdE: BoolE = frontierE(this)
  // val borderE:BoolE= xorR(transfer(e(this))) //pour tester le calcul du rayon
  val nbCh: UintV = nbccBis(Comm.apexV(f(brdE))) //first use of brdE
  // val nbCh: UintV =nbcc(Comm.apexV(f(brdE))) //first use of brdE
  val meetV = nbCh > 1 //makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$1
  //meetV.setName("meetV")
  val emptyRhomb: BoolE = insideErhombusE(notE(brdE)) //second use of brdE, check that there is a totally empty rhombus between two blobs
  emptyRhomb.setName("emptyRhomb")
  val twoAdjBlob: BoolE = insideE(frontierV(brdE)) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
  twoAdjBlob.setName("twoAdjBlob")
  val meetE: BoolE = andE(emptyRhomb, twoAdjBlob) //we've got to be able to not have to write calls to andE!!
  //meetE.setName("meetE")


}

