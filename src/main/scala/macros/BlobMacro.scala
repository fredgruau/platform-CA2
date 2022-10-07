package macros

import compiler.AST._
import compiler.ASTL._
import compiler._
import macros.Compute._
import macros.SReduce.frontierEDef

/** macro used specifically to compute the blob predicate */
object BlobMacro {

  /** carryV is not written as a macro to avoid generating too many macro */
  def carryV(b0: BoolV, b1: BoolV, b2: BoolV): BoolV = (b0 & b1) | (b2 & (b0 | b1))

  /** sum3V is not written as a macro to avoid generating too many macro */
  def sum3V(b0: BoolV, b1: BoolV, b2: BoolV): UintV = concat2UI(b0 ^ b1 ^ b2, carryV(b0, b1, b2))

  /** From a boolfV, computes the number of true connected components, likely to be reused for BlobE, BlobVe */
  val nbccDef: Fundef1[(T[V, F], B), (V, UI)] = {
    val vf = p[T[V, F], B]("ringAroundV")
    val asInt: UintV = concatR(vf)
    asInt.setName("asInt");
    val (n0, n1, n2, n3, n4, n5) = (elem(0, asInt), elem(1, asInt), elem(2, asInt), elem(3, asInt), elem(4, asInt), elem(5, asInt))
    //   val nbChanges: UintV =sum3(n0|n1,n2|n3,n4|n5)
    val nbChanges: UintV = sum3V(n0 | n1, n2 | n3, n4 | n5)
    Fundef1("nbcc", nbChanges, vf)
  }

  /** wrapper to  Call nbcc  */
  def nbcc(b: BoolfV): UintV = new Call1(nbccDef, b) with UintV


  /** useless wrapper to nbcc, to test a non root main. */
  val nbccBis: Fundef1[(T[V, F], B), (V, UI)] = {
    val vB = p[T[V, F], B]("blobis")
    val nbChanges: UintV = nbcc(vB) + nbcc(vB)
    Fundef1("nbccbis", nbChanges, vB)
  }

  /** wrapper to  Call nbcc  */
  def nbccBis(b: BoolfV): UintV = new Call1(nbccBis, b) with UintV


  /** From a boolfV, computes the number of true connected components */
  val nbcc2: Fundef1[(V, B), (V, UI)] = {
    val vB = p[V, B]("blob")
    val asInt: UintV = concatR(Comm.apexV(f(xorR(transfer(e(vB))))))
    asInt.setName("asInt");
    val (n0, n1, n2, n3, n4, n5) = (elem(0, asInt), elem(1, asInt), elem(2, asInt), elem(3, asInt), elem(4, asInt), elem(5, asInt))
    val nbChanges: UintV = sum3V(n0 | n1, n2 | n3, n4 | n5)
    Fundef1("nbcc2", nbChanges, vB)
  }

  /** wrapper to  Call nbcc  */
  def nbcc2(b: BoolV): UintV = new Call1(nbcc2, b) with UintV
}