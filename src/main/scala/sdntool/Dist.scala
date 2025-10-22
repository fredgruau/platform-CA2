package sdntool


import compiler.AST._
import compiler.SpatialType.{BoolVe, _}
import compiler.ASTBfun.{addRedop, andRedop, isneg, minSignRedop, orRedop, p, redop, xorRedop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.ASTLt._
import compiler.Circuit.hexagon
import compiler._
import compiler.SpatialType._
import dataStruc.{BranchNamed, Named}
import progOfStaticAgent.{Homogeneize, Leader}
import progOfmacros.Comm.neighborsSym
import progOfmacros.{Grad, Wrapper}
import progOfmacros.Wrapper.{borderS, exist, existS, inside, neqUI2L}
import progOfmacros.RedT.cacEndomorph
import sdn.{ BlobVe, Force, LayerS, MovableAgV, MoveC, MoveC1, MoveC2, MuStruct, One,  Stratify, addGcenter, carrySysInstr}
import sdn.Util.{addLt, addLtSI}
import sdn.addVor
/**
 * @param source
 * @param bitSize sometimes more than 3 bits are necessary
 *  * computes distance to source
 */
class MuDist(val source: MuStruct[V, B],val bitSize:Int) extends Dist(bitSize) {
  override def inputNeighbors: List[MuStruct[_ <: Locus, _ <: Ring]] = List(source)
  /** calcul directement a partir de la distance
   *  si y a une différence de valeur entre deux Vertex adjacent d'un edge donné,
   * todo devrait  se faire aussi dans slopeDelta pour simplifier
   * par contre on ne peut pas le calculer a partir de slopelt, sinon ca bugge
   * pour des pb de miror qui nécessite de passer par des vertices*/
  val voisinDiff:BoolE=(addLtSI(muis.pred)).diff
  //val iambig=source.asInstanceOf[QPointFields].tripletonV
  //val incrOld = cond(delayedL(source.muis.munext), cond(iambig,sign(opp+1),sign(opp)), delta)
  val incr = cond(delayedL(source.muis.munext), sign(opp), deltag)
  source match{
    case ag: sdn.ForceAg[V]=> //adds a slow constraint to avoid vortex creation
      /** moving to forbidden would create a source in a negative distance
       * that would hence not be able to correctly decrease its distance level */
      val forbidden:BoolV= ASTLfun.isneg(muis.pred)
      val  slow=ag.CancelFlipIf(One(false),forbidden ) _// agent should not invade cells where distance is negative
      ag.addConstraint("slow",'w',slow)
    case _ =>
  }
  // val deefF=new ConstLayer[F, B](1, "def")
}

/**
 * code common to any distances
 * @param n  number of bits
 */
abstract class Dist(val n:Int)extends MuStruct [V,SI] {
 /** 0, +1 ot -1  we update with small delta:either increment or decrement*/
  val incr: ASTLt[V, SI]
  override val muis: LayerS[V, SI] = new LayerS[V, SI](n, "0") //we put 5 bits so as to obtain continuity
  { override val next: AST[(V, SI)] = delayedL(this.pred + incr)(this.mym)  }
  val (sloplt: BoolVe, deltag, level, gap) = Grad.slopDelta(muis.pred)
  val slopgt= neighborsSym(sloplt)
  val opp = -(muis.pred)
  /** spurious vortex occurs outside chip.borderF.df, so we have to and with chip.borderF.df in order to prevent false detection of vortex bug */
  val vortex: BoolF = chip.borderF.df & andR(transfer(cacEndomorph(xorRedop[B]._1, sloplt)))
  def showMe={
    shoow( gap, sloplt, level, vortex) // necessary so as to use all parameters returned by slopeDeltashoow(vortex)
    shoowText(deltag,List())
    val deefV = new ConstLayer[V, B](1, "def")
    buugif(vortex) //todo, mettre aussi un bug si y a un écart  sur la source plus grand K en valeur absolue, K reste a déterminer
  }

  /** we may have to replace muis by isV in order to obtain a force that can acts on BoolEv Agents, and not only BoolV agents */
  val repulse: Force = new Force() {
    override def actionV(ag: MovableAgV): MoveC = {
      val hasNearer: BoolV = Wrapper.exist(sloplt & neighborsSym(e(ag.muis)))
      val hasFurther = Wrapper.exist(slopgt & neighborsSym(e(ag.muis)))
      val oui = MoveC1( ag.muis & hasFurther & ~hasNearer,
        neighborsSym(sloplt) & ag.bf.brdVeIn) //extends towards increasing value of distances and empties everywhere possible.
      val non = MoveC1(ag.muis & hasNearer, sloplt & ag.bf.brdVeIn  ) //falseVe
      MoveC2(oui, non)
    }
  }
  val repulseVor: Force = new Force() {
    override def actionV(ag: MovableAgV): MoveC = {
      val hasNearer: BoolV = Wrapper.exist(sloplt & ag.bf.qqnEnFace)
      val hasFurther = Wrapper.exist(slopgt & ag.bf.qqnEnFace)
      /** positive moves takes place is weWantItEmpty, and vertice was occupied*/
      val weWantItEmpty=hasFurther & ~hasNearer
      val oui = MoveC1(ag.muis & weWantItEmpty ,
        neighborsSym(sloplt) & ag.bf.brdVeIn) //extends towards increasing value of distances and empties everywhere possible.
      /** negative moves takes place is weWantItEmpty, and vertice was NOT occupied
       * if it was occupied, we should first remove nearer if it has some nearer*/
      val non = MoveC1(cond(ag.muis,hasNearer,weWantItEmpty), e(fromBool(false))/*sloplt & ag.bf.brdVeIn*/  ) //falseVe
      MoveC2(oui, non)
    }
  }
}
/** computes distance to gabriel centers added to the distance of that gabriel center to seeds i.e, distance to nearest neighbors */
class MuDistGcenter(val source:MovableAgV with addDist with addGcenter) extends Dist(6) {
  override def inputNeighbors = List(source.d)
  val incr: ASTLt[V, SI] = cond(delayedL(source.bve.meetE2), sign(opp+2), cond(delayedL(source.bve.meetV), sign(opp), deltag))
}

/** adds  distance to particles */
trait addDist {
  self: MuStruct[V, B] => //adds a distance to a LayerV , also limit its movement so as to avoid vortices
  val d = new MuDist(self,3);
  //show(d); les show doivent etre fait dans le main
}

/** adds gabriel centers, uses blob computation on slopelt, works like magic */


/** adds distance to gcentern */
trait addDistGcenter {
  self: MovableAgV with addDist with addGcenter=>
  val dg = new MuDistGcenter(this)
  //show(d); les show doivent etre fait dans le main
}

/** computes distance to gabriel centers also taking into account distance to voronoi, in order to avoid vibration
 * caused by the fact that gabriel centers are discontinuous*/
class MuDistGcenterVor(val source:MovableAgV with addDist with addVor with addGcenter) extends Dist(6) {
  override def inputNeighbors = List(source.vor,source.gc)
  val incr: ASTLt[V, SI] = cond(delayedL(source.bve.meetV), sign(opp), cond(delayedL(source.bve.meetE2), sign(opp+2), deltag))
}

/** adds distance to gcentern corrected by voronoi*/
trait addDistGcenterVor {
  self: MovableAgV with addDist with addVor with addGcenter=>
  val dgv = new MuDistGcenterVor(this)
  //show(d); les show doivent etre fait dans le main
}



/** contains show(dist) otherwise, class Dist is not compiled at all, because not used from the root */
trait DistSimplerT {
  self: Layer[(V, B)] => //adds a distance to a LayerV todo, it should also limit its movement
  val dist = new DistSimpler(self);
 // show(dist); les show doivent etre fait dans le main

}

/** a simpler version of distance, which does not uses send */
class DistSimpler(val source: Layer[(V, B)]) extends Layer[(V, SI)](3, "0") with ASTLt[V, SI] {
  /*val level: BoolV = elem(2, this);*/
  val grad: IntVe = neighbors(this) - e(this)
  val lt: BoolVe = ltSI(grad)
  val eq: BoolE = ~reduce[E, V, B](orRedop[B], transfer(lt)) //its equal if it is neither lt nor gt
  val delta: IntV = reduce(minSignRedop, sign(extend(4, grad) + 2)) //we need to add 2, using one more bit, in order to add modulo 16 and not 8
  val next: ASTLt[V, SI] = this + cond(source.asInstanceOf[BoolV], sign(-this), delta) //faudrait en faire une macro qui prends delta, source et dist et renvoie distNext
  show(lt, eq)
}

