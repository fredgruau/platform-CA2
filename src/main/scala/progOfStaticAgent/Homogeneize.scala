package progOfStaticAgent

import dataStruc.{BranchNamed, Named}
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
  part.shoowText(part.dg.muis.pred,List())
  part.shoow(part.prioDet)
  part.shoow(part.prioDetYes)
  part.shoowText(part.prio,List())
  part.shoowText(part.prioYes,List())
  part.shoowText(part.prioYesNotQuiescent,List())
  part.shoow(part.triggeredRepulse)
  part.shoow(part.triggeredExplore)
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
class Seed() extends  MovableAgentV with BlobVouE with QpointConstrain with BlobConstrain { // override def displayConstr:Boolean=true
  shoow(muis)
  shoow(flipOfMove, flipAfterLocalConstr)
  //  for (v<-realFlipCancel.values) shoow(v) //display intermediate, decreasing  flip value
  shoow(meetE, meetV, nbCc, lateBrdE)
  //shoow(doubleton,singleton,tripleton)
}

/** moves as much as possible, todo put it in its own file */
class Flies2 extends Seed {
  final val explore=introduceNewPriority()
  force(explore, "explore",'x', Force.total)
}

/**adds gabriel center,  distance to gabriel center, and then repulsive force*/
class Homogen() extends Flies2 with DistT with gCenter with DistGcenter
{  final val homogeneize=introduceNewPriority()
  force(homogeneize,"repulse",'|',dg.repulse)//specific forces applied to Flies
  val triggeredRepulse =moves(homogeneize).values.head.triggered
  val triggeredExplore =moves(explore).values.head.triggered
  //showMoves
};


