package sdntool


import compiler.AST.{Layer, _}
import compiler.SpatialType.{BoolVe, _}
import compiler.ASTBfun.{addRedop, andRedop, isneg, minSignRedop, orRedop, p, redop, xorRedop}
import compiler.ASTL._
import compiler.ASTLfun.{e, _}
import compiler.ASTLt._
import compiler.Circuit.hexagon
import compiler.{ASTLt, chip, _}
import compiler.SpatialType._
import dataStruc.{BranchNamed, Named}
import progOfStaticAgent.{Homogeneize, Leader}
import progOfmacros.Comm.neighborsSym
import progOfmacros.{Grad, Wrapper}
import progOfmacros.Wrapper.{borderS, exist, existS, inside, neqUI2L}
import progOfmacros.RedT.cacOld
import sdn.{BlobOld, BlobVe, Force, LayerS, MovableAgentV, MoveC, MoveC1, MoveC2, MuStruct, One, QPointFields, Stratify, addGcenter, carrySysInstr}
import sdn.Util.{addLt, addLtSI, newaddBlobVe}

/**
 * @param source
 * @param bitSize sometimes more than 3 bits are necessary
 *  * computes distance to source
 */
class MuDist(val source: MuStruct[V, B],val bitSize:Int)extends MuStruct [V,SI] {
  override def inputNeighbors: List[MuStruct[_ <: Locus, _ <: Ring]] = List(source)
  override val muis:LayerS[V, SI]  = new LayerS[V, SI](bitSize, "0")
     { override val next: AST[(V, SI)] =delayedL(this.pred + incr)(this.mym) }
  val opp = - (muis.pred)
  val (sloplt: BoolVe, delta, level, gap) = Grad.slopDelta(muis.pred)
  /** calcul directement si y a une différence de valeur entre deux Vertex adjacent,
   * todo devrait  se faire aussi dans slopeDelta pour simplifier
   * par contre on ne peut pas le calculer a partir de slopelt, sinon ca bugge
   * pour des pb de miror qui nécessite de passer par des vertices*/
  val voisinDiff:BoolE=(addLtSI(muis.pred)).diff
  val iambig=source.asInstanceOf[QPointFields].tripletonV
  val incrOld = cond(delayedL(source.muis.munext), cond(iambig,sign(opp+1),sign(opp)), delta)
  val incr = cond(delayedL(source.muis.munext), sign(opp), delta)
  val vortex: BoolF = andR(transfer(cacOld(xorRedop[B]._1, sloplt))) // andR( transfer(clock(sloplt) ^ anticlock(sloplt))); //transitive circular lt

  source match{
    case ag: sdn.Agent[V]=> //adds a slow constraint to avoid vortex creation
      /** moving to forbidden would create a source in a negative distance
       * that would hence not be able to correctly decrease its distance level */
      val forbidden:BoolV= ASTLfun.isneg(muis.pred)
      val  slow=new ag.CancelFlipIf(One(false),forbidden, ag.flipOfMove ) // agent should not invade cells where distance is negative
      ag.constrain("slow",'w',slow)
    case _ =>
  }

  def showMe={shoow(delta,gap, sloplt, level) // necessary so as to use all parameters returned by slopeDelta
    shoow(vortex)
    buugif(vortex) //todo, mettre aussi un bug si y a un écart de 4 sur la source
  }

 // val deefF=new ConstLayer[F, B](1, "def")
}

/** computes distance to gabriel centers added to the distance of that gabriel center to seeds i.e, distance to nearest neighbors */
class MuDistGcenter(val source:MovableAgentV with addDist with addGcenter) extends MuStruct [V,SI] {
  override def inputNeighbors: List[MuStruct[_ <: Locus, _ <: Ring]] = List(source.d)
  override val muis: LayerS[V, SI] = new LayerS[V, SI](6, "0") //we put 5 bits so as to obtain continuity
  { override val next: AST[(V, SI)] = delayedL(this.pred + incr)(this.mym)  }
   val (sloplt: BoolVe, deltag, level, gap) = Grad.slopDelta(muis.pred)

  val deefV = new ConstLayer[V, B](1, "def")
  //val incrOldOld = cond(delayedL(gc.gCenterV), sign(closedFit), cond(delayedL(gc.gCenterE), sign(closedFit + 2), deltag))
   val opp = -(muis.pred)
   val incr = cond(delayedL(source.gc.meetV), sign(opp), cond(delayedL(source.gc.meetE2), sign(opp+2), deltag))
  /** spurious vortex occurs outside chip.borderF.df, so we have to and with chip.borderF.df in order to prevent false detection of vortex bug */
  val vortex: BoolF = chip.borderF.df & andR(transfer(cacOld(xorRedop[B]._1, sloplt))) // andR( transfer(clock(sloplt) ^ anticlock(sloplt))); //transitive circular lt
  def showMe={
    shoow( gap, sloplt, level, vortex) // necessary so as to use all parameters returned by slopeDeltashoow(vortex)
    shoowText(deltag,List())
    buugif(vortex) //todo, mettre aussi un bug si y a un écart  sur la source plus grand K en valeur absolue, K reste a déterminer
  }
  /** we may have to replace muis by isV in order to obtain a force that can acts on BoolEv Agents, and not only BoolV agents */
  val repulse: Force = new Force() {
    override def actionV(ag: MovableAgentV): MoveC = {
      val hasNearer: BoolV = Wrapper.exist(sloplt & neighborsSym(e(ag.muis)))
      val hasFurther = Wrapper.exist(neighborsSym(sloplt) & neighborsSym(e(ag.muis)))
      val oui = MoveC1(ag.muis & hasFurther & ~hasNearer,
        neighborsSym(sloplt) & ag.brdVe) //extends towards increasing value of distances and empties everywhere possible.
      val non = MoveC1(ag.muis & hasNearer, sloplt & ag.brdVe  ) //falseVe
      MoveC2(oui, non)
    }
  }
}

/** adds  distance to particles */
trait addDist {
  self: MuStruct[V, B] => //adds a distance to a LayerV , also limit its movement so as to avoid vortices
  val d = new MuDist(self,3);
  //show(d); les show doivent etre fait dans le main
}

/** adds gabriel centers, uses blob computation on slopelt, works like magic */
trait gCenterOld{
  self:MovableAgentV with addDist=> //there is a distance already

 /** on calcule  brdE directement depuis la distance aux seeds,
  * parceque  a cause de pb de radius
  * et de miror update qui se fait juste sur les boolV
 le calcul de brdE a partir de brdEv est faux. */
  val dBrdE:BoolE=(addLtSI(d.muis.pred)).diff  //ya moyen de faire ca mieux en calculant
  val oldb=newaddBlobVe(d.sloplt,dBrdE) //on passe donc en meme temps le BrdVe et BrdE
  val b=new BlobVe(muis,dBrdE,d.sloplt) //on passe donc en meme temps le BrdVe et BrdE


  val issV:BoolV=this.asInstanceOf[MovableAgentV].isV

  /** true for doubletons */
  val next2Source: BoolE =exist(transfer(e(issV)))
  val gCenterV=  b.meetV
  /** we discard spurious gcenters */
  val meetE2:BoolV=existS[E,V](delayedL(b.meetE))& ~ issV //ca en exclus trop sans doute.
  val gCenterE=meetE2
  val dd: MuDist =d
}

/** adds distance to gcentern */
trait addDistGcenter {
  self: MovableAgentV with addDist with addGcenter=>
  val dg = new MuDistGcenter(this)
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

