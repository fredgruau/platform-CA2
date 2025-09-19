package progOfStaticAgent

import compiler.ASTL.{anticlock, delayedL, sym, transfer}
import compiler.ASTLfun.e
import compiler.SpatialType.{BoolV, BoolVe, BoolVf}
import compiler.{AST, ASTBfun, ASTLt, B, E, Locus, Ring, SI, T, V}
import dataStruc.{BranchNamed, Named}
import progOfmacros.Comm.neighborsSym
import progOfmacros.RedT.cac
import progOfmacros.Wrapper
import progOfmacros.Wrapper.exist
import sdn._
import sdntool.{DistGcenter, DistT, gCenter}

/**illustrate the working of repulsion combined with exploration  */
class Homogeneize() extends LDAG with Named with BranchNamed
{ val part=new Homogen()
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

class Convergent extends Homogen with Lead{
  final val stabilize=introduceNewPriority()
  force(stabilize,"balance",'_',myleader.balance)//specific forces applied to Flies
  shoow(myleader.muis)
}

/**
 *
 * @param source quasiparticle
 * identifies a vertex within source */
class Leader(source: Seed)extends MuStruct [V,B] {
  override def inputNeighbors: List[MuStruct[_ <: Locus, _ <: Ring]] = List(source)

  /** should be initialized globally,  exactly as source */
  val sourceNext = source.muis.next.asInstanceOf[BoolV]
  /** true if leader is no longer on the support of its source */
  val sourceHasMoved = source.isV & ~sourceNext
  val neighborSourceNext: BoolVe = sym(e(sourceNext))
  /** by hypothesis, neighborSourceNext is a segment, electedNeigbor is just the first element of this segment */
  val electedNeigbor: BoolVf = cac(ASTBfun.delta, neighborSourceNext)

  override val muis: LayerS[V, B] = new LayerS[V, B](1, "global") {
    /** we have to consider sym to finally retrieve the new leader. */
      override val next: AST[(V, B)] = delayedL(exist(sym(anticlock(electedNeigbor))))(this.mym)
  }

  import compiler.ASTLfun.fromBool //pour avoir la conversion implicite de boolean vers boolVe
 /** annule le mouvement si stable, donc seul no est défini */
  val balance: Force = new Force() {
    override def actionV(ag: MovableAgentV): MoveC = {

      val non = MoveC1(fromBool[V](false)&muis, fromBool[T[V,E]](false)&fromBool[T[V,E]](false)) //ne va pas empty sur leader, juste pour tester
    non
    }
  }
}
trait Lead {
  self: Seed => //adds a leader to seed ,
  val myleader=new Leader(this);
  //show(d); les show doivent etre fait dans le main
}