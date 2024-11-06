package sdn

import compiler.ASTL.{sym, transfer}
import compiler.ASTLfun.{andR, apex, e, f, neighbors, orR, v}
import compiler.SpatialType.{BoolE, BoolEf, BoolF, BoolV, BoolVe}
import compiler.{AST, ASTLt, B, E, F, Locus, T, V}
import progOfCA.{MovableAg, RandInt2, Vagent, rando}
import progOfmacros.Comm.{apexV, neighborsSym}
import progOfmacros.Compute
import progOfmacros.Wrapper.{exist, existS, inside, insideS}
import progOfmacros.RedT.clock2

trait QPointify {
  self: Vagent => //quasiPoints are blobs.
  /** true for the vertices of a qpt consiting exactly of one vertices */
    val noNeighbor=inside(neighborsSym(notVe))
  val singleton: BoolV =noNeighbor  & isV
  /** true if both apex vertices of the edge are empty */
  val bothApexEmpty: BoolE = ~orR(apex[V, E, B](f(isV)))
  /** true for the edge inside qpt consiting exactly of two vertices */
  val doubleton: BoolE = insideS[V, E](isV) & bothApexEmpty
  val doubletonV:BoolV = existS[E,V](doubleton)
  val doubletonEf:BoolEf=f(doubleton)
  val isApexV:BoolV=exist[F,V](apexV(doubletonEf))

  /** true for the face inside a qpt consiting exactly of three adjacent  vertices */
  val tripleton: BoolF = insideS[V, F](isV)
  val tripletonV:BoolV = existS[F,V](tripleton)
}

class Qpoint extends MovableAg[V] with Vagent with QPointify with rando with RandInt2{
  /** true if selected by a random angle among 12 */
  val effRandDir:ASTLt[T[V,E],B] =rand.randDir & isVe
  val touchedByRandDir: BoolV =exist(neighborsSym(effRandDir))

  /** true if qpoint wants to flip towards all directions */
  lazy val ringOfFlip:BoolV= inside(neighborsSym(e(currentFlip))) & singleton

  /** cancel ring growth of singleton, exept if it happens to be selected by random angles thereafter, we will be able to shring flip not forming a ring */
  val breakRingFlip:Constr2 = new LocCtrKeepFlipIf(One(false)){
    override def where: BoolV ={Compute.imply(exist(neighborsSym(e(ringOfFlip))),touchedByRandDir) }
  }

  val next2NonSingleton=exist(neighborsSym(e(doubletonV|tripletonV)))

  /** cancel growth for non singleton, exept for doubleton, on appex */
  val leq4:Constr2 = new LocCtrKeepFlipIf(One(false)){override def where: BoolV = Compute.imply(next2NonSingleton,isApexV)}
    /** singleton cannot flip */
    val diseaperSingle:Constr2 = new LocCtrCancelFlipIf(One(true)){override def where: BoolV = singleton  }


    val extend2side: BoolVe = clock2(transfer(sym(v(doubleton) & rand.randSide)))


  /** used to compute flip cancelation depending on impact */
}
