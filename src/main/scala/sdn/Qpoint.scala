package sdn

import compiler.ASTL.{delayedL, sym, transfer}
import compiler.ASTLfun.{andR, apex, e, f, neighbors, orR, v}
import compiler.SpatialType.{BoolE, BoolEf, BoolF, BoolV, BoolVe}
import compiler.{AST, ASTLt, B, E, F, Locus, T, V}
import dataStruc.BranchNamed
import progOfCA.{MovableAg, Vagent, rando}
import progOfmacros.Comm.{apexV, neighborsSym}
import progOfmacros.Compute
import progOfmacros.Compute.implique
import progOfmacros.Wrapper.{exist, existS, inside, insideS}
import progOfmacros.RedT.clock2

trait QPointify {
  self: Vagent => //quasiPoints are blobs.
  /** true for the vertices of a qpt consiting exactly of one vertices */
  val noNeighbor = inside(neighborsSym(notVe))
  val singleton: BoolV = noNeighbor & isV
  /** true if both apex vertices of the edge are empty */
  val bothApexEmpty: BoolE = ~orR(apex[V, E, B](f(isV)))
  /** true for the edge inside qpt consiting exactly of two vertices */
  val doubleton: BoolE = insideS[V, E](isV) & bothApexEmpty
  val doubletonV: BoolV = existS[E, V](doubleton)
  val doubletonEf: BoolEf = f(doubleton)
  val isApexV: BoolV = exist[F, V](apexV(doubletonEf))

  /** true for the face inside a qpt consiting exactly of three adjacent  vertices */
  val tripleton: BoolF = insideS[V, F](isV)
  val tripletonV: BoolV = existS[F, V](tripleton)
}

class Qpoint extends MovableAg[V] with Vagent with QPointify with rando {
  /** true if selected by a random angle among 12 */
  val effRandDir: ASTLt[T[V, E], B] = rand.randDir & isVe
  val touchedByRandDir: BoolV = exist(neighborsSym(effRandDir))

  /** true if qpoint wants to flip towards all directions, lazy because flip is not available yet */
  def ringOfFlip: BoolV = inside(neighborsSym(e(currentFlip))) & singleton
  def breakRingOfFlip:BoolV=implique(exist(neighborsSym(e(ringOfFlip))), touchedByRandDir)
  /** cancel ring growth of singleton, exept if it happens to be selected by random angles thereafter, we will be able to shring flip not forming a ring */
  val breakRingFlip: Constr = new KeepFlipIfWithDef(One(false)){def loc:BoolV=breakRingOfFlip} //le boolV ne sera pas instancié tant que on ne contraindra pas
  val next2NonSingleton = exist(neighborsSym(e(doubletonV | tripletonV)))
  /** cancel growth for non singleton, exept for doubleton, on appex */
  val leq4: Constr = new KeepFlipIf(One(false),implique(next2NonSingleton, isApexV))
  /** singleton cannot flip */
  val diseaperSingle = new CancelFlipIf(One(true),singleton)


  /** doubleton cannot flip two*/
  val diseaperDouble = new MutKeepFlipIf(One(true),doubleton) with BranchNamed {}


  val extend2side: BoolVe = clock2(transfer(sym(v(doubleton) & rand.randSide)))


  /** used to compute flip cancelation depending on impact */
}
