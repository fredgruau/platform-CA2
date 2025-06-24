package sdn

import compiler.ASTL.{delayedL, sym, transfer}
import compiler.ASTLfun.{andR, apex, e, f, imply, neighbors, orR, v}
import compiler.SpatialType.{BoolE, BoolEf, BoolF, BoolV, BoolVe}
import compiler.{AST, ASTLt, B, E, F, Locus, T, V}
import dataStruc.{BranchNamed, Named}
import progOfLayer.Sextexrect.chooseMinOf
import sdn.rando
import sdn.{MovableAg, MovableAgentV}
import progOfmacros.Comm.{apexV, neighborsSym}
import progOfmacros.Compute
import progOfmacros.Compute.{implique, impluq}
import progOfmacros.Wrapper.{exist, existS, inside, insideS, not}
import progOfmacros.RedT.clock2
/** field needed to compute the contstraint of  a quasipoint, and possibly elsewehere */
trait QPointFields {
  self: MovableAgentV => //quasiPoints are blobs.
  /** true for the vertices of a qpt consiting exactly of one vertices */
  val noNeighbor = inside(neighborsSym(notVe))
  val singleton: BoolV = noNeighbor & isV
  val nonsingleton= ~ singleton  & isV
  /** true if both apex vertices of the edge are empty */
  val bothApexEmpty: BoolE = not(orR(apex[V, E, B](f(isV))))
  /** true for the edge inside qpt consiting exactly of two vertices */
  val doubleton: BoolE = insideS[V, E](isV) & bothApexEmpty
  val doubletonV: BoolV = existS[E, V](doubleton)
  val isApexV: BoolV = exist[F, V](apexV(f(doubleton)))
  /** true for the face inside a qpt consiting exactly of three adjacent  vertices */
  val tripleton: BoolF = insideS[V, F](isV)
  val tripletonV: BoolV = existS[F, V](tripleton)
  val choose=chooseMinOf(prio)
}

/** defines all the constraint that should be met by a quasipoint, except for blobs which might not be necessary if Gabriel centers are computed. */
trait  QpointConstrain extends QPointFields with rando{
self: MovableAgentV => //a quasi point  is a movableAgentV
/** if ring, fix one direction  todo to be replaced by sextex*/
  /** true if selected by a random angle among 12 */
  //val effRandDir: BoolVe = rand.randDir & isVe
  /** true if a random direction  points to it */
  //val touchedByRandDir: BoolV = exist(neighborsSym(effRandDir))

  /** will choose neighbor with smallest flip priority  */
  val  sexKeepFlipIf=new Constr(Array(this), null,flipOfMove)with Named with BranchNamed {
    //val whereto:BoolVe= ~ e(singleton) |choose
    val whereto:BoolVe= imply(e(singleton),choose)
    /** where = places where flips is still valid after the constraint newFlip<-olcFlip&where
     * defined has a method, in order allow definition prior to intanciation of needed field, such as flip.  */
    override val where: BoolV = inside(neighborsSym(whereto))
  }
  constrain("growToTwo",sexKeepFlipIf)
  /** true for neighbors of non singleton*/
//  val next2NonSingleton = exist(neighborsSym(e(doubletonV | tripletonV)))
  val next2NonSingleton = exist(neighborsSym(e(nonsingleton)))
  /**  cancel growth for non singleton, exept for doubleton, on appex, this needs a tournament*/
  val leqQuatre: Constr ={
   new KeepFlipIf(One(false),implique(next2NonSingleton, isApexV),flipOfMove) with Named with BranchNamed {}}
  constrain("leqQuatre",leqQuatre)
  /** singleton cannot flip */
  val diseaperSingle = new CancelFlipIf(One(true),singleton,flipOfMove)
  constrain("diseaperSingle",diseaperSingle)
  /**a doubleton cannot flip both vertices*/
  val diseaperDouble = new MutKeepFlipIf(One(true),doubleton,flipOfMove) with BranchNamed {}
  constrain("diseaperDouble",diseaperDouble)
  /** cannot grow from two, to four on both apex */
  val appearDouble = new MutApexKeepFlipIf(One(false),doubleton,flipOfMove) with Named with BranchNamed {}
  constrain("appearDouble",appearDouble)
  /**  a tripleton cannot flip its three vertices*/
  val diseaperTriple=new TriKeepFlipIf(One(true),tripleton,flipOfMove) with BranchNamed {}
  constrain("diseaperTriple",diseaperTriple)

  //val extend2side: BoolVe = clock2(transfer(sym(v(doubleton) & rand.randSide)))


  /** used to compute flip cancelation depending on impact */
}
