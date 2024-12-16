package progOfmacros

import compiler.{B, E, T}
import compiler.AST.{Call1, Call2, Fundef1, Fundef2, Layer, pL}
import compiler.ASTLfun._
import compiler.ASTL._
import compiler.SpatialType._
import compiler.Circuit.hexagon
import compiler._
import progOfmacros.RedT.{cac, cacOld}

/** contains macro computing information used to perseved topological invariants, such as nbcc, or quasiPoint */
object Topo {
  /** From a booleV, computes the number of true connected components, can be reused for BlobE, BlobVe */
  val nbccDef: Fundef1[(T[V, E], B), (V, UI)] = {
    val ve = pL[T[V, E], B]("ringAroundV")
    val vf: BoolVf = cac(ASTBfun.delta, ve)
    val asInt: UintV = concatR(vf)
    asInt.setName("asInt");
    val (n0, n1, n2, n3, n4, n5) = (elt(0, asInt), elt(1, asInt), elt(2, asInt), elt(3, asInt), elt(4, asInt), elt(5, asInt))
    val nbChanges: UintV = sum3V(n0 | n1, n2 | n3, n4 | n5)
    Fundef1("topo.nbcc", nbChanges, ve)
  }
 
  /** wrapper to  Call nbcc */
  def nbcc(b: BoolVe): UintV = new Call1[(T[V, E], B), (V, UI)](nbccDef, b) with UintV

/** From a border (boolE), computes the number of true connected components*/
  val nbccVDef: Fundef1[(E, B), (V, UI)] = {
    val border = pL[E, B]("borderE")
    val borderVe=transfer(v(border))
    val vf: BoolVf = cac(ASTBfun.delta, borderVe)
    val asInt: UintV = concatR(vf)
    asInt.setName("asInt");
    val (n0, n1, n2, n3, n4, n5) = (elt(0, asInt), elt(1, asInt), elt(2, asInt), elt(3, asInt), elt(4, asInt), elt(5, asInt))
    val nbChanges: UintV = sum3V(n0 | n1, n2 | n3, n4 | n5)
    Fundef1("topo.nbcc", nbChanges, border)
  }

  /** wrapper to  Call nbccVdef */
  def nbccV(b: BoolE): UintV = new Call1[(E, B), (V, UI)](nbccVDef, b) with UintV


  /** macro used specifically to compute the blob predicate */

  /** produces a boolVe border that takes into account what happens on the frontier of the chip: if there is a blob on the border, it says that there is a border */
  val brdInDef: Fundef2[(E, B), (V, B), (T[V, E], B)] = {
    val brd = pL[E, B]("brd");
    val is = pL[V, B]("is")
    val brdIn: BoolVe = cond(chip.borderVe.df, transfer(v(brd)), e(is)) //this will produce a border for blobs next to the chip frontier
    Fundef2("topo.brdin", brdIn, brd, is)
  }

  def brdin(brd: BoolE, is: BoolV): BoolVe = new Call2[(E, B), (V, B), (T[V, E], B)](brdInDef, brd, is) with BoolVe

}