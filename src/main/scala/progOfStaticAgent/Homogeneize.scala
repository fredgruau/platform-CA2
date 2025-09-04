package progOfStaticAgent

import dataStruc.{BranchNamed, Named}
import sdn._
import sdntool.{DistGcenter, DistT, gCenter}

/**combines flies with the computation of distance, adds a constraints of slowliness
  */
class Homogeneize() extends LDAG with Named with BranchNamed
{ val part=new Seed() with DistT with gCenter with DistGcenter{
  move(dg.repulse) //specific forces applied to Flies
};
  part.shoow(part.d.muis) //necessaire pour la reachabilité
  part.showConstraint
  part.shoow(part.gCenterV,part.gCenterE)
  part.shoow(part.dg.muis.pred)
}


class Seed() extends  MovableAgentV with BlobVouE with QpointConstrain with BlobConstrain { // override def displayConstr:Boolean=true
  shoow(muis)
  shoow(flipOfMove, flipAfterLocalConstr)
  //  for (v<-realFlipCancel.values) shoow(v) //display intermediate, decreasing  flip value
  shoow(meetE, meetV, nbCc, lateBrdE)
  //shoow(prioRand.eq,prio.lt)
  //shoow(doubleton,singleton,tripleton)
}