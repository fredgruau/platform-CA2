package progOfCA

import compiler.AST.{Call1, Fundef1, Layer, pL}
import compiler.ASTLfun._
import compiler.ASTL._
import compiler.SpatialType._
import compiler.Circuit.hexagon
import compiler._
import BlobMacro._
import compiler.ASTLt.ConstLayer
import progOfmacros.Comm
import progOfmacros.Compute._
import progOfmacros.RedS.{exist, frontier}

/** computes  V-meeting points and E-meeting points in the case of a brave simple BoolV  Blob  */
trait BlobV extends BoolV { //the blob is not necessarily a layer
  self: BoolV =>
  val brd: BoolE = frontier(this)

  val nbCh: UintV = nbcc(apex(f(brd))) //nbccBis(Comm.apexV(f(brd))) //first use of brdE
  // val nbCh: UintV =nbcc(Comm.apexV(f(brdE))) //first use of brdE
  val meetV: BoolV = nbCh > 1 //makes an implicit conversion of nbCh from unsigned int to signed int. shoudl take into acount only nbch$1
  val emptyRhomb: BoolE = ~exist[F, E](exist[E, F](brd)) //second use of brdE, check that there is a totally empty rhombus between two blobs
  val twoAdjBlob: BoolE = exist[V, E](exist[E, V](brd)) //third use of brdE, check that there is two adjacent blobs next to the empty rhombus
  val meetE: BoolE = emptyRhomb & twoAdjBlob //we've got to be able to not have to write calls to andE!!
}

/** uses the blob to grow voronoi region stoping the growth just before merge happens */
class GrowVor() extends ConstLayer[V, B](1, "global") with ASTLt[V, B] with BlobV {
  //val next: BoolV = orR(neighbors(this)) & (~meetV) & (~exist[E, V](meetE)) //only radius 0 computation, because communication is handled in macro

  show(this, nbCh) // meetE, meetV,
}

/** macro used specifically to compute the blob predicate */
object BlobMacro {

  /** carryV is not written as a macro to avoid generating too many macro */
  def carryV(b0: BoolV, b1: BoolV, b2: BoolV): BoolV = (b0 & b1) | (b2 & (b0 | b1))

  /** sum3V is not written as a macro to avoid generating too many macro */
  def sum3Vold(b0: BoolV, b1: BoolV, b2: BoolV): UintV = concat2UI(b0 ^ b1 ^ b2, carryV(b0, b1, b2))

  def sum3V(b0: BoolV, b1: BoolV, b2: BoolV): UintV = (b0 ^ b1 ^ b2) :: carryV(b0, b1, b2)

  /** From a boolfV, computes the number of true connected components, likely to be reused for BlobE, BlobVe */
  val nbccDef: Fundef1[(T[V, F], B), (V, UI)] = {
    val vf = pL[T[V, F], B]("ringAroundV")
    val asInt: UintV = concatR(vf)
    asInt.setName("asInt");
    val (n0, n1, n2, n3, n4, n5) = (elt(0, asInt), elt(1, asInt), elt(2, asInt), elt(3, asInt), elt(4, asInt), elt(5, asInt))
    //   val nbChanges: UintV =sum3(n0|n1,n2|n3,n4|n5)
    val nbChanges: UintV = sum3V(n0 | n1, n2 | n3, n4 | n5)
    Fundef1("blob.nbcc", nbChanges, vf)
  }

  /** wrapper to  Call nbcc */
  def nbcc(b: BoolVf): UintV = new Call1[(T[V, F], B), (V, UI)](nbccDef, b) with UintV


  /** useless wrapper to nbcc, to test a non root main. */
  val nbccBis: Fundef1[(T[V, F], B), (V, UI)] = {
    val vB = pL[T[V, F], B]("blobis")
    val nbChanges: UintV = nbcc(vB) + nbcc(vB)
    nbChanges.setName("nbChange")
    Fundef1("blob.nbccbis", nbChanges, vB)
  }

  /** wrapper to  Call nbcc */
  def nbccBis(b: BoolVf): UintV = new Call1[(T[V, F], B), (V, UI)](nbccBis, b) with UintV


  /** From a boolfV, computes the number of true connected components */
  val nbcc2: Fundef1[(V, B), (V, UI)] = {
    val vB = pL[V, B]("blob")
    val asInt: UintV = concatR(Comm.apexV(f(xorR(transfer(e(vB))))))
    asInt.setName("asInt");
    val (n0, n1, n2, n3, n4, n5) = (elt(0, asInt), elt(1, asInt), elt(2, asInt), elt(3, asInt), elt(4, asInt), elt(5, asInt))
    val nbChanges: UintV = sum3V(n0 | n1, n2 | n3, n4 | n5)
    Fundef1("blob.nbcc2", nbChanges, vB)
  }

  /** wrapper to  Call nbcc */
  def nbcc2(b: BoolV): UintV = new Call1[(V, B), (V, UI)](nbcc2, b) with UintV
}