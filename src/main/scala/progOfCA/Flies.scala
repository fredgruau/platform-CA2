package progOfCA

import compiler.AST.Layer
import compiler.ASTBfun.{andRedop, orRedop}
import compiler.ASTL.transfer
import compiler.ASTLfun.{orR, reduce}
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.{BoolE, BoolV}
import compiler.{AST, ASTLt, B, E, V, repr}
import sdn.Util.addBlobV
import sdn.{BlobConstrain, BlobV, BlobVouE, Compar, Force, MovableAg, MovableAgentV, QpointConstrain}

import java.util.HashMap
import java.util


/** flies is constrained with blob, so as to be preserved , with qpoint so that their support remains of size <3 */
class Flies() extends  MovableAgentV  with QpointConstrain with BlobVouE with BlobConstrain
{  move(Force.total)
   //updateFlip(flipCreatedByMoves) //calcul de flip0

// val nutrig=appearDouble.mutrig
  /** we create val so as to show them */


  refineFlip() //calcul de flip1,flip2,....
 for (v<-rawFlipCancel.values) shoow(v) //display intermediate, decreasing  flip value
  for (v<-realFlipCancel.values) shoow(v) //display intermediate, decreasing  flip value
 // shoow(meetE,meetV,nbCc,lateBrdE)
  shoow(is,NisV)
  shoow(doubleton,singleton)
  shoow(next2NonSingleton,doubletonV,tripletonV,isApexV)
  val defE=new ConstLayer[E, B](1, "def")
  val twoLt: BoolE =reduce(andRedop[B], prio.lt)
  shoow(twoLt,touchedByRandDir,prioRand.lt,prioRand)
  shoow(prioRand.eq)
  //shoow(sloplt,level,twoLt,dopp,se,grad3,grad6)
  buugif(twoLt&defE) //marche
  //shoow(appearDouble.mutrigv)
  //shoow(bugE)

}




