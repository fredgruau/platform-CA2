package progOfmacros

import compiler.ASTLfun.e
import compiler.SpatialType._
import compiler.AST._
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.hexagon
import compiler.{V, _}
import progOfmacros.Topo.nbccDef

object Util {
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

  /** from a BoolV randBit, produces a BoolVe randBit, allowing to select among the 6 directions */
  private val randN6def: Fundef1[(V, B), (T[V, E], B)] = { //yavait un bug, on a suivi la méthode de deboggage
    // conssitant a nommer les variables contenant les résultats intermediiares, afin de dechifrer le code compilé.
    val b = pL[V, B]("randNeigh")
    val nasI: UintV = concatR(neighbors(b)).asInstanceOf[UintV]
    nasI.setName("neighborasInt");
    val (r0, r1, r2, r3, r4, r5) = (elt(0, nasI), elt(1, nasI), elt(2, nasI), elt(3, nasI), elt(4, nasI), elt(5, nasI))
    //use the two first bits to select among 3 directions.
    val s0 = (r0 & r1) //ends by 11
    val s1 = (r0 & ~(r1)) //end by O1
    val s2 = (~(r0) & r1) //ends by 10
    s0.setName("s0")
    s1.setName("s1")
    s2.setName("s2")
    val fail = (~(r0) & ~(r1)) //ends by 00 failure has a proba 1/4
    fail.setName("fail")
    // same process  from the two next bits.
    val t0 = (r2 & r3)
    val t1 = (r2 & ~(r3))
    val t2 = (~(r2) & r3)
    t0.setName("t0")
    t1.setName("t1")
    t2.setName("t2")
    // in case s0s1s2=000, we OR it with t0t1t2, so as to augment the proba that s0s1s2!=000 to 15/16
    val ss0 = (s0 | (fail & t0))
    val ss1 = (s1 | (fail & t1))
    val ss2 = (s2 | (fail & t2))
    ss0.setName("ss0")
    ss1.setName("ss1")
    ss2.setName("ss2")
    val fail2 = (fail & ~(r2) & ~(r3)) //global failure has now a proaba 1/16
    val tt0 = ss0 & ~r4;
    val tt1 = ss1 & ~r4;
    val tt2 = ss2 & ~r4; //usse the fifth bit r4 to sselect among 6 dir.
    tt0.setName("tt0")
    tt1.setName("tt1")
    tt2.setName("tt2")
    val sss0 = ss0 & r4;
    val sss1 = ss1 & r4;
    val sss2 = ss2 & r4 //using the cond construct
    sss0.setName("sss0")
    sss1.setName("sss1")
    sss2.setName("sss2")
    val res = send[V, E, B](List(sss0, sss1, sss2, tt0, tt1, tt2))
    Fundef1("util.randN6", res, b)
  }

  def randN6(b: BoolV): BoolVe = new Call1[(V, B), (T[V, E], B)](randN6def, b) with BoolVe

  /** from a BoolV randBit, produces a BoolVe randBit, allowing to select among the 6 directions */
  private val randN12def: Fundef1[(V, B), (T[V, E], B)] = { //yavait un bug, on a suivi la méthode de deboggage
    // conssitant a nommer les variables contenant les résultats intermediiares, afin de dechifrer le code compilé.
    val b = pL[V, B]("randNeigh")
    val nasI: UintV = concatR(neighbors(b)).asInstanceOf[UintV]
    nasI.setName("neighborasInt");
    val (r0, r1, r2, r3, r4, r5) = (elt(0, nasI), elt(1, nasI), elt(2, nasI), elt(3, nasI), elt(4, nasI), elt(5, nasI))
    //use the two first bits to select among 3 directions.
    val s0 = (r0 & r1) //ends by 11
    val s1 = (r0 & ~(r1)) //end by O1
    val s2 = (~(r0) & r1) //ends by 10
    s0.setName("s0")
    s1.setName("s1")
    s2.setName("s2")
    val fail = (~(r0) & ~(r1)) //ends by 00 failure has a proba 1/4
    fail.setName("fail")
    // same process  from the two next bits.
    val t0 = (r2 & r3)
    val t1 = (r2 & ~(r3))
    val t2 = (~(r2) & r3)
    t0.setName("t0")
    t1.setName("t1")
    t2.setName("t2")
    // in case s0s1s2=000, we OR it with t0t1t2, so as to augment the proba that s0s1s2!=000 to 15/16
    val ss0 = (s0 | (fail & t0))
    val ss1 = (s1 | (fail & t1))
    val ss2 = (s2 | (fail & t2))
    ss0.setName("ss0")
    ss1.setName("ss1")
    ss2.setName("ss2")
    val fail2 = (fail & ~(r2) & ~(r3)) //global failure has now a proaba 1/16
    val tt0 = ss0 & ~r4;
    val tt1 = ss1 & ~r4;
    val tt2 = ss2 & ~r4; //usse the fifth bit r4 to sselect among 6 dir.
    tt0.setName("tt0")
    tt1.setName("tt1")
    tt2.setName("tt2")
    val sss0 = ss0 & r4;
    val sss1 = ss1 & r4;
    val sss2 = ss2 & r4 //using the cond construct
    sss0.setName("sss0")
    sss1.setName("sss1")
    sss2.setName("sss2")
    val res6 = send[V, E, B](List(sss0, sss1, sss2, tt0, tt1, tt2))
    // val res12= cond(e(r5),res6,enlarge(res6))
    val res12 = res6 | andLB2R(e(r5), clock(clock(res6)))
    Fundef1("util.randN12", res12, b)
  }

  def randN12(b: BoolV): BoolVe = new Call1[(V, B), (T[V, E], B)](randN12def, b) with BoolVe

}
