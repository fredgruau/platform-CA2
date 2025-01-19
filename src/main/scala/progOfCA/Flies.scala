package progOfCA

import compiler.AST.Layer
import compiler.ASTBfun.{andRedop, orRedop}
import compiler.ASTL.transfer
import compiler.ASTLfun.{orR, reduce}
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.{BoolE, BoolV}
import compiler.{AST, ASTLt, B, E, V, repr}
import sdn.Util.addBlobV
import sdn.{BlobConstrain, BlobV, BlobVouE, Compar, Force, MovableAg, MovableAgentV, MoveC1, QpointConstrain}

import java.util.HashMap
import java.util


/** flies is constrained
 * 1-with blob, so that particles do not merge nor split
 * 2-with qpoint so that their support remains of size <=3 */
class Flies() extends  MovableAgentV with BlobVouE with QpointConstrain with BlobConstrain
{  // override def displayConstr:Boolean=true
 move(Force.total) //specific forces applied to Flies




 // refineFlip() //calcul de flip1,flip2,....
 shoow(is)
 shoow(flipOfMove,flipAfterLocalConstr)
//  for (v<-realFlipCancel.values) shoow(v) //display intermediate, decreasing  flip value
 shoow(meetE,meetV,nbCc,lateBrdE)
 shoow(prioRand.eq,prioRand,prio.lt)
shoow(doubleton,singleton)
 shoow(next2NonSingleton,leqQuatre.where, isApexV)
  //shoow(next2NonSingleton,doubletonV,tripletonV,isApexV)


 // shoow(touchedByRandDir,)
  //shoow(sloplt,level,twoLt,dopp,se,grad3,grad6)
 val twoLt: BoolE =reduce(andRedop[B], prio.lt)
 val defE=new ConstLayer[E, B](1, "def")
 buugif(twoLt&defE) //marche
  //shoow(appearDouble.mutrigv)
  //shoow(bugE)

}




