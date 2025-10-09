/*
package progOfStaticAgent

import compiler.ASTBfun.andRedop
import compiler.ASTLfun.reduce
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.BoolE
import compiler.{B, E}
import sdn._
import sdntool.{DistT}


/** flies is constrained
 * 1-with blob, so that particles do not merge nor split
 * 2-with qpoint so that their support remains of size <=3 */
class Flies() extends  MovableAgentV with BlobVouE with QpointConstrain with BlobConstrain
{  // override def displayConstr:Boolean=true
 //
 final val explore=introduceNewPriority()
 force(explore, "Explore",'Y', Force.total) //specific forces applied to Flies
 shoow(muis)
 shoow(flipOfMove,flipAfterLocalConstr)
//  for (v<-realFlipCancel.values) shoow(v) //display intermediate, decreasing  flip value
 shoow(meetE,meetV,nbCc)
 //shoow(prioRand.eq,prio.lt)
//shoow(doubleton,singleton,tripleton)
/** contient les premiers caractéres de chaque nom de contraintes */

}
*/




