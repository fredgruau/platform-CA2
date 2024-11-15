package progOfCA

import compiler.AST.Layer
import compiler.ASTBfun.{andRedop, orRedop}
import compiler.ASTL.transfer
import compiler.ASTLfun.{orR, reduce}
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.{BoolE, BoolV}
import compiler.{AST, ASTLt, B, E, V, repr}
import sdn.{Qpoint}

import java.util.HashMap
import java.util


/** we test simple movement, using a single agents*/
class Flies() extends Qpoint //with Blobify with QPointify
{  val b:Boolean=true
  move(Force.total)

  updateFlip(initialFlip) //calcul de flip0
  constrain(leq4)
  constrain(diseaperSingle)
  constrain(breakRingFlip)
  val nutrig=diseaperDouble.mutrig
  val where=diseaperDouble.where
  val tmp=diseaperDouble.tmp
  constrain(diseaperDouble)
  refineFlip //calcul de flip1,flip2,....

  shoow(nutrig, where,tmp)
  for (v<-flip.values) shoow(v) //display intermediate, decreasing  flip value

  shoow(is)
  shoow(NisV)
  shoow(doubleton,singleton)
  shoow(next2NonSingleton,isApexV)
  val defE=new ConstLayer[E, B](1, "def")
  val twoLt: BoolE =reduce(andRedop[B], prioLt)
  shoow(twoLt,touchedByRandDir,prioLt,level,prioRand)
  //shoow(sloplt,level,twoLt,dopp,se,grad3,grad6)
  buugif(twoLt&defE) //marche pas, je pensais que oui, mais en fait non.
  //shoow(bugE)

}




