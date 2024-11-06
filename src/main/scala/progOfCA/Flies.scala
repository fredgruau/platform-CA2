package progOfCA

import compiler.AST.Layer
import compiler.ASTBfun.{andRedop, orRedop}
import compiler.ASTL.transfer
import compiler.ASTLfun.{orR, reduce}
import compiler.SpatialType.{BoolE, BoolV}
import compiler.{AST, ASTLt, B, V}
import sdn.Qpoint

import java.util.HashMap
import java.util
//import scala.collection.convert.ImplicitConversions.`map AsJavaMap`

/** we test simple movement, using a single agents*/
class Flies() extends Qpoint //with Blobify with QPointify
{ val b:Boolean=true
  move(Force.total)
  constrain(breakRingFlip)
  constrain(leq4)
  constrain(diseaperSingle)
  updateFlip(setFlip) //calcul de flip0
  refineFlip //calcul de flip1,flip1,....
  for (v<-flip.values) shoow(v) //display intermediate, decreasing  flip value
  shoow(is)
  shoow(NisV)
  shoow(doubleton)
  shoow(next2NonSingleton,isApexV)

  val twoLt: BoolE =reduce(andRedop[B], transfer(sloplt))
  shoow(sloplt,level,twoLt,dopp,se,grad3,grad6)
  buugif(twoLt)
  //shoow(bugE)

}




