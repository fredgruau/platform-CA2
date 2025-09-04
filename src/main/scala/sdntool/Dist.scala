package sdntool


import compiler.AST.{Layer, _}
import compiler.SpatialType.{BoolVe, _}
import compiler.ASTBfun.{addRedop, andRedop, isneg, minSignRedop, orRedop, p, redop, xorRedop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.ASTLt._
import compiler.Circuit.hexagon
import compiler.{ASTLt, _}
import compiler.SpatialType._
import dataStruc.{BranchNamed, Named}
import progOfmacros.Comm.neighborsSym
import progOfmacros.Grad
import progOfmacros.Wrapper.{borderS, inside, neqUI2L}
import progOfmacros.RedT.cacOld
import sdn.Force.TOTAL_PRIO
import sdn.{Blob, BlobOld, BlobVe, Force, LayerS, MovableAgentV, MoveC, MoveC1, MuStruct, One, Stratify, carrySysInstr}
import sdn.Util.addBlobVe

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
  //gabriel centers can be directly obtain simply by computing Vmeeting-point of the blob, using sloplt
  // and also Emeeting points, nearest to the source.
 // val b = addBlobVe(sloplt) //could be not used.

  val incr = cond(delayedL(source.muis.munext), sign(opp), delta)
  val vortex: BoolF = andR(transfer(cacOld(xorRedop[B]._1, sloplt))) // andR( transfer(clock(sloplt) ^ anticlock(sloplt))); //transitive circular lt
  bugif(vortex) //todo, mettre aussi un bug si y a un écart de 4 sur la source
  //adds a slow constraint to avoid vortex creation
  source match{
    case ag: sdn.Agent[V]=>
      val forbidden:BoolV= ASTLfun.isneg(muis.pred)
      val  slow=new ag.CancelFlipIf(One(false),forbidden, ag.flipOfMove ) // agent should not invade cells where distance is negative
      ag.constrain("slow",'w',slow)
    case _ =>
  }
   shoow(delta,gap, sloplt, level) // necessary so as to use all parameters returned by slopeDelta
  shoow(vortex)

 // val deefF=new ConstLayer[F, B](1, "def")
}

/** computes distance to gabriel centers added to the distance of that gabriel center to seeds i.e, distance to nearest neighbors */
class MuDistGcenter(val gc:gCenter) extends MuStruct [V,SI]{
  override def inputNeighbors: List[MuStruct[_ <: Locus, _ <: Ring]] = List(gc.dd)
  override val muis:LayerS[V, SI]  = new LayerS[V, SI](5, "0") //we put 5 bits so as to obtain continuity
  { override val next: AST[(V, SI)] =delayedL(this.pred + incr)(this.mym) }
   val closedFit: ASTLt[V, SI] =  gc.dd.muis.pred -(muis.pred) //dois rester a zero au début puisque d et dg augmente en meme temps,
  val fit:ASTLt[V, SI]= cond(delayedL(gc.gCenterV), closedFit, cond(delayedL(gc.gCenterE), closedFit + 2, 0)) //doit rester negatif et < 4
  val (sloplt: BoolVe, delta, level, gap) = Grad.slopDelta(muis.pred)
 val gcenterEorV=gc.gCenterE | gc.gCenterV
   val deefV=new ConstLayer[V, B](1, "def")
  val incr = cond(delayedL(gc.gCenterV), sign(closedFit),cond(delayedL(gc.gCenterE), sign(closedFit + 2), delta))
  val vortex: BoolF = andR(transfer(cacOld(xorRedop[B]._1, sloplt))) // andR( transfer(clock(sloplt) ^ anticlock(sloplt))); //transitive circular lt
  bugif(vortex) //todo, mettre aussi un bug si y a un écart  sur la source plus grand K en valeur absolue, K reste a déterminer
  shoow(delta,gap, sloplt, level,gcenterEorV) // necessary so as to use all parameters returned by slopeDelta
  shoow(vortex)
  val repulse:Force=new Force(){
    val prio=TOTAL_PRIO-1
    override def actionV(ag: MovableAgentV): MoveC = MoveC1(ag.isV,
      neighborsSym(sloplt) & ag.brdVe)//extends towards increasing value of distances and empties everywhere possible.
  }
  // val deefF=new ConstLayer[F, B](1, "def")
}

/** adds  distance to particles */
trait DistT {
  self: MuStruct[V, B] => //adds a distance to a LayerV , also limit its movement so as to avoid vortices
  val d = new MuDist(self,5);
  //show(d); les show doivent etre fait dans le main
}
/** adds gabriel centers, uses blob computation on slopelt, works like magic */
trait gCenter{
  self:DistT=> //there is a distance already
  val b=addBlobVe(d.sloplt)
  val gCenterV=b.meetV
  val gCenterE=b.meetE2
  val dd: MuDist =d
}

/** adds distance to gcentern */
trait DistGcenter {
  self: gCenter=>
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

