package progOfmacros

import compiler.ASTLfun.e
import compiler.SpatialType._
import compiler.AST._
import compiler.ASTBfun.rotUI
import compiler.ASTL.{transfer, _}
import compiler.ASTLfun._
import compiler.Circuit.hexagon
import compiler._
import progOfmacros.Wrapper.{border, borderS}
import progOfmacros.Topo.nbccDef
import sdn.Util.{addSym, addSymUI}

object Util {
  /** This macro computes the identity, exept that we will modify the generated java code, so as to add a wrap instead of a miror */
  private val torusifyDef: Fundef1[(V, B), (V, B)] = {
    val b = pL[V, B]("randmiror")
    Fundef1("util.torusify", b, b) //identity function, we will add the torusify code directly in the java.
    }
  def torusify(b: BoolV): BoolV = new Call1[(V, B), (V, B)](torusifyDef, b) with BoolV


  /** compute the next value of a random bit, using the neighbors and a tested combination of ors, and xors
   * which does not have short 256 cycle */
  private val randDef: Fundef1[(V, B), (V, B)] = {
    val b = pL[V, B]("randNeigh")
    val nasI: UintV = concatR(neighbors(b)).asInstanceOf[UintV]
    nasI.setName("neighborasInt");
    val (n0, n1, n2, n3, n4, n5) = (elt(0, nasI), elt(1, nasI), elt(2, nasI), elt(3, nasI), elt(4, nasI), elt(5, nasI))
    //val randBit=xorn(orn(n0,n1,n2),n3,n4,n5)
    val randBit: ASTLt[V, B] = (n0 | n1 | n2) ^ n3 ^ n4 ^ n5
    randBit.setName("randBit");
    Fundef1("util.rand", randBit, b)
  }

  def randNext(b: BoolV): BoolV = new Call1[(V, B), (V, B)](randDef, b) with BoolV

  /** from a BoolV randBit, produces a BoolVe randBit, allowing to select among 12 directions
   * which select among 6 main directions, and a rotation of those*/
  private val randN12def: Fundef1[(V, B), (T[V, E], B)] = { //yavait un bug, on a suivi la méthode de deboggage
    // conssitant a nommer les variables contenant les résultats intermediiares, afin de dechifrer le code compilé.
    val b = pL[V, B]("randNeigh")
  //  val voisins: UintVe =addSymUI(e(b)).symUI
  // val voisins: BoolVe =addSym(e(b)).sym  //on peut pas faire référence a une macro depuis une macro.
  val voisins: BoolVe =transfer(sym(transfer(e(b))))
    val nasI: UintV = concatR(voisins).asInstanceOf[UintV]
  //  val nasI: UintV = concatR(neighbors(b)).asInstanceOf[UintV]
    nasI.setName("neighborasInt");
    val (r0, r1, r2, r3, r4, r5) = (elt(0, nasI), elt(1, nasI), elt(2, nasI), elt(3, nasI), elt(4, nasI), elt(5, nasI))
    //use the two first bits to select among 3 directions.
    val List(s0, s1, s2, fail) = unary(r0, r1) //proba(fail)  is 1/4
    val List(t0, t1, t2, fail2) = unary(r2, r3)
    val failtotal: BoolV = fail & fail2
    val rand3 = andLB2R(fail, t0.asInstanceOf[UintV] :: t1 :: t2) | (s0.asInstanceOf[UintV] :: s1 :: s2)
    val rand6 = andLB2R(r4, rand3) :: andLB2R(~r4, rand3)
    val rand12 = rand6 | andLB2R(r5, unop(rotUI, rand6))
    val res12 = send[V, E, B](List(elt(0, rand12), elt(1, rand12), elt(2, rand12), elt(3, rand12), elt(4, rand12), elt(5, rand12)))
    Fundef1("util.randN12", res12, b)
  }

  def randN12(b: BoolV): BoolVe = new Call1[(V, B), (T[V, E], B)](randN12def, b) with BoolVe

  private val randE2def: Fundef1[(V, B), (T[E, V], B)] = { //yavait un bug, on a suivi la méthode de deboggage
    // conssitant a nommer les variables contenant les résultats intermediiares, afin de dechifrer le code compilé.
    val b = pL[V, B]("rand")
    val bE: BoolE = borderS[V, E, B](b)
    val res2: BoolEv = send[E, V, B](List(bE, ~bE))
    Fundef1("util.randE2", res2, b)
  }

  def randE2(b: BoolV): BoolEv = new Call1[(V, B), (T[E, V], B)](randE2def, b) with BoolEv
}
