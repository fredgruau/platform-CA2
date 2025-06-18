package progOfCA

import compiler.AST.Layer
import compiler.ASTBfun.{andRedop, orRedop}
import compiler.ASTL.{sym, transfer}
import compiler.ASTLfun.{orR, reduce}
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.{BoolE, BoolV}
import compiler.{AST, ASTLt, B, E, V, repr}
import progOfmacros.Comm.apexV
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

 shoow(is)
 shoow(flipOfMove,flipAfterLocalConstr)
//  for (v<-realFlipCancel.values) shoow(v) //display intermediate, decreasing  flip value
 shoow(meetE,meetV,nbCc,lateBrdE)
 shoow(prioRand.eq,prioRand,prio.lt)
shoow(doubleton,singleton)
 shoow(next2NonSingleton,leqQuatre.where, isApexV)
 shoow(choose)
 shoow(prioRand.ltApex)
 val twoLt: BoolE =reduce(andRedop[B], prio.lt)
 val defE=new ConstLayer[E, B](1, "def")
 buugif(twoLt&defE) //marche verifie que y a au max un seul des deux coté plus petit
val mutrig=appearDouble.mutrig;
 val chekLtIfMutrig=appearDouble.chekLtIfMutrig
 shoow(appearDouble.chekLtIfMutrig,appearDouble.mutrig)


 //shoow(toto4,toto3)
  //shoow(bugE)
}




