package sdn

import compiler.ASTL.{delayedL, send, sym, transfer}
import compiler.ASTLfun.{andR, apex, concatR, e, elt, f, imply, neighbors, orR, v}
import compiler.SpatialType.{BoolE, BoolEf, BoolF, BoolV, BoolVe, UintV, UintVe}
import compiler.{AST, ASTLt, B, E, F, Locus, T, V}
import dataStruc.{BranchNamed, Named}
import progOfLayer.Sextexrect.{chooseMaxOf, weakCmpProdZero, weakCmpProdtwo}
import sdn.rando
import sdn.{MovableAg, MovableAgentV}
import progOfmacros.Comm.{apexV, insideBall, neighborsSym}
import progOfmacros.Compute
import progOfmacros.Compute.{concat3V, implique, impluq}
import progOfmacros.Wrapper.{exist, existS, inside, insideS, not}
import progOfmacros.RedT.clock2
import sdn.Util.addSymUI
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
  //val choose: BoolVe =chooseMinOf(prio)
  val choose: BoolVe =chooseMaxOf(prioYesNotQuiescent,4)




}

/** defines all the constraint that should be met by a quasipoint, except for blobs which might not be necessary if Gabriel centers are computed. */
trait  QpointConstrain extends QPointFields with rando{
self: MovableAgentV => //a quasi point  is allways a movableAgentV
  /**
   *
   * @param feature
   * return a boolV true throughout the seed,
   * if and only if feature is also true throughout the seed
   */
   def forallize(feature:BoolV)={
      insideBall(imply(muis, feature))
 }

  /** will choose neighbor with higest flip priority  */
  val  sexKeepFlipIf=new Constr(Array(this), null, flipOfMove) with Named with BranchNamed {
    //val whereto:BoolVe= ~ e(singleton) |choose
    val whereto:BoolVe= imply(e(singleton),choose)
    /** where = places where flips is still valid after the constraint newFlip<-olcFlip&where
     * defined has a method, in order allow definition prior to intanciation of needed field, such as flip.  */
    override val where: BoolV = inside(neighborsSym(whereto))
  }
  constrain("growToTwo",'x',sexKeepFlipIf)
  /** true for neighbors of non singleton*/
//  val next2NonSingleton = exist(neighborsSym(e(doubletonV | tripletonV)))
  val next2NonSingleton = exist(neighborsSym(e(nonsingleton)))
  /**  cancel growth for non singleton, exept for doubleton, on appex, this needs a tournament*/
  val leqQuatre: Constr ={
   new KeepFlipIf(One(false),implique(next2NonSingleton, isApexV),flipOfMove) with Named with BranchNamed {}}
  constrain("leqQuatre",'q',leqQuatre)
  /** singleton cannot flip */
  val diseaperSingle = new CancelFlipIf(One(true),singleton,flipOfMove)
  constrain("diseaperSingle",'s',diseaperSingle)
  /**a doubleton cannot flip both vertices*/
  val diseaperDouble = new MutKeepFlipIf(One(true),doubleton,flipOfMove) with BranchNamed {}
  constrain("diseaperDouble",'d',diseaperDouble)
  /** cannot grow from two, to four on both apex */
  val appearDouble = new MutApexKeepFlipIf(One(false),doubleton,flipOfMove) with Named with BranchNamed {}
  constrain("appearDouble",'a',appearDouble)
  /**  a tripleton cannot flip its three vertices*/
  val diseaperTriple=new TriKeepFlipIf(One(true),tripleton,flipOfMove) with BranchNamed {}
  constrain("diseaperTriple",'t',diseaperTriple)

  //val extend2side: BoolVe = clock2(transfer(sym(v(doubleton) & rand.randSide)))


  /** used to compute flip cancelation depending on impact */
}
