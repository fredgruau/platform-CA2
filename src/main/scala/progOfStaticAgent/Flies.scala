package progOfStaticAgent

import compiler.ASTBfun.andRedop
import compiler.ASTLfun.reduce
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.BoolE
import compiler.{B, E}
import sdn._


/** flies is constrained
 * 1-with blob, so that particles do not merge nor split
 * 2-with qpoint so that their support remains of size <=3 */
class Flies() extends  MovableAgentV with BlobVouE with QpointConstrain with BlobConstrain
{  // override def displayConstr:Boolean=true
 move(Force.total) //specific forces applied to Flies

 shoow(is)
 shoow(flipOfMove,flipAfterLocalConstr)
//  for (v<-realFlipCancel.values) shoow(v) //display intermediate, decreasing  flip value
 shoow(meetE,meetV,nbCc,lateBrdE)
 shoow(prioRand.eq,prio.lt)
 shoowText(prioRand,"0","1","2")

shoow(doubleton,singleton,tripleton)
 shoow(next2NonSingleton,leqQuatre.where, isApexV)
 shoow(choose)

 val twoLt: BoolE =reduce(andRedop[B], prio.lt)
 val defE=new ConstLayer[E, B](1, "def")
 buugif(twoLt&defE) //marche verifie que y a au max un seul des deux coté plus petit
val mutrig=appearDouble.mutrig;
 val chekLtIfMutrig=appearDouble.chekLtIfMutrig
 shoow(appearDouble.chekLtIfMutrig,appearDouble.mutrig)
 shoow(prioRand.lt3)
 val codeConstraint: Iterable[String] =constrs.keys.toList.map(_.charAt(0).toString)
 shoowText(allFlipCancel,codeConstraint.toList)
 //shoow(toto4,toto3)
  //shoow(bugE)
}




