package progOfStaticAgent

import compiler.ASTL.{anticlock, clock, delayedL, sym, transfer}
import compiler.ASTLfun.{cond, e, imply}
import compiler.SpatialType.{BoolV, BoolVe, BoolVf}
import compiler.{AST, ASTBfun, ASTLt, B, E, Locus, Ring, SI, T, V}
import dataStruc.{BranchNamed, Named}
import progOfmacros.Comm.{adjacentBall, insideBall, neighborsSym}
import progOfmacros.RedT.cac
import progOfmacros.Wrapper
import progOfmacros.Wrapper.{border, borderS, exist, existS, inside, insideS, smoothen, smoothen2, testShrink}
import sdn._
import sdntool.{DistGcenter, DistT, gCenter}

/**illustrate the working of repulsion combined with exploration  */
class Homogeneize() extends LDAG with Named with BranchNamed
{ val part=new Convergent()
  part.shoowText(part.d.muis,List()) //necessaire pour la reachabilité
  part.shoow(part.dBrdE)
  part.showConstraint
  part.showMoves
  part.showPositiveMoves
  part.shoow(part.gCenterV,part.gCenterE)
  //part.shoowText(part.dg.muis.pred,List())
  part.shoow(part.prioDet)
  part.shoow(part.prioDetYes)
  part.shoowText(part.prio,List())
  part.shoowText(part.prioYes,List())
  part.shoowText(part.prioYesNotQuiescent,List())
  part.shoow(part.prio.ltApex)
  part.shoow(part.choose)
  part.shoow(part.b.selle)
  part.shoow(part.b.upwardSelle)
  part.shoow(part.b.downwardSelle)
  part.shoow(part.b.twoAdjBlob)
  part.shoow(part.b.emptyRhomb)
  part.shoow(part.b.lateBrdVe)
  part.shoow(part.b.lateBrdE)
  //  part.shoow(part.toto)
  part.shoow(part.b.vf)
  part.shoowText(part.b.nbCc,List())
  part.shoowText(part.prioRand,List() )

}

/** adds quasipoint and blob constraints */
class Seed extends  MovableAgentV with BlobVouE with QpointConstrain with BlobConstrain { // override def displayConstr:Boolean=true
  shoow(muis)
  shoow(flipOfMove, flipAfterLocalConstr)
  //  for (v<-realFlipCancel.values) shoow(v) //display intermediate, decreasing  flip value
  shoow(meetE, meetV, nbCc, lateBrdE)
  //shoow(doubleton,singleton,tripleton)
}


/** moves as much as possible, todo put it in its own file */
class Flies2 extends Seed {
  /** exploring priority */
  final val explore=introduceNewPriority()
  force(explore, "explore",'x', Force.total)
}

/**adds gabriel center,  distance to gabriel center, and then repulsive force*/
class Homogen() extends Flies2 with DistT with gCenter with DistGcenter
{  /** homogeneizing priority */
  final val homogeneize=introduceNewPriority()
  force(homogeneize,"repulse",'|',dg.repulse)//specific forces applied to Flies
  shoowText(dg.muis, List())

  //showMoves
};

class Convergent extends Homogen // with Lead //pas besoin de leader pour le moment
{
  final val stabilize=introduceNewPriority()
   /** border of qparticle  where dg diminishes */
    val brdVeSloped=brdVe&dg.sloplt
  /** around isV, adds Vertices on the otherside of brdVeslopped */
    val isVplus=isV | exist(transfer(sym(transfer(brdVeSloped))))
  /** add vertex  if three neighbors are on */
  val isVsmoothed=smoothen(isVplus)
  /** computes the Vf bool and yes that is right*/
  val isVtest=testShrink(isVplus)
  /** add vertex  if four neighbors are on, bugs, more restrictive therefore, than smoothen */
  val isVsmoothed2=isVplus| exist(isVtest)

  shoow(isVplus,isVsmoothed,isVsmoothed2,isVtest)  /** true for one seed if on its whole border dg diminishes */
val stable1Old=muis & inside(imply(brdVe,dg.sloplt))
  val stable1=muis & insideBall(isVsmoothed2)
  val stable2=forallize(stable1)&isV
  val balance: Force = new Force() {
    import compiler.ASTLfun.fromBool
    override def actionV(ag: MovableAgentV): MoveC = {
      /** pure negative move */
      val yes=MoveC1(false,false)
      /** if stable2 , this will cancel movement of lower priority, */
      val no = MoveC1(stable2, e(stable2)&brdVe)
      MoveC2(yes,no)
    }
  }
  force(stabilize,"balance",'_',balance)//specific forces applied to Flies
  shoow(stable1,stable2)
}

/**
 *
 * @param source quasiparticle
 * identifies a vertex within source, may be not usefull after all,
 * since it is arguably easier to compute stuf on the whole particle support*/
class Leader(source: Seed)extends MuStruct [V,B] {
  override def inputNeighbors: List[MuStruct[_ <: Locus, _ <: Ring]] = List(source)

  /** should be initialized globally,  exactly as source */
  val sourceNext = source.muis.next.asInstanceOf[BoolV]
  /** true if leader is no longer on the support of its source */
  val sourceOfLeaserHasMoved = source.isV & ~sourceNext & delayedL( muis.pred)
  /** extends sourceHasMoved to the adjacent Vertices */
  val sourceMovedWide = adjacentBall(sourceOfLeaserHasMoved)

  val neighborSourceNext: BoolVe = transfer(sym(transfer(e(sourceNext))) ) & e(delayedL( muis.pred))
  /** by hypothesis, neighborSourceNext is a segment, electedNeigbor is just the first element of this segment */
  val electedNeigbor1: BoolVf = cac(ASTBfun.delta, neighborSourceNext)
  val electedNeigbor2: BoolVe=anticlock(electedNeigbor1)
  val elected3: BoolV =  exist(transfer(sym(transfer(electedNeigbor2))))
  override val muis: LayerS[V, B] = new LayerS[V, B](1, "global") {
    /** we have to consider sym to finally retrieve the new leader. */
      override val next: AST[(V, B)] = delayedL(cond(sourceMovedWide,elected3,this.pred))(this.mym)
  }

  shoow(electedNeigbor2,electedNeigbor1,sourceMovedWide,neighborSourceNext,elected3)

  import compiler.ASTLfun.fromBool //pour avoir la conversion implicite de boolean vers boolVe
 /** annule le mouvement si stable, donc seul no est défini */
  val balance: Force = new Force() {
    override def actionV(ag: MovableAgentV): MoveC = {
      val yes=MoveC1(false,false) //convergent is a pure negative move
      val no = MoveC1(muis, false) //ne va pas empty sur leader, juste pour tester
    MoveC2(yes,no)
    }
  }
}
trait Lead {
  self: Seed => //adds a leader to seed ,
  val myleader=new Leader(this);
  //show(d); les show doivent etre fait dans le main
}