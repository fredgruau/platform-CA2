package progOfCA

import compiler.ASTBfun.andRedop
import compiler.ASTLfun.reduce
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.BoolE
import compiler.{B, E, V}
import dataStruc.BranchNamed
import sdn.Util.{addLt, randUintV}
/** tests the lt macro, containts a bugif */
class   Testlt() extends ConstLayer[V, B](1, "global")  with BranchNamed{
 // val rand1 = new Rand();  val rand2 = new Rand()
  val prioRand = randUintV(6) //rand1::rand2
  val toto=addLt(prioRand)
 val deefE=new ConstLayer[E, B](1, "def") //forced to be named defE

 val twoLt: BoolE =reduce(andRedop[B], toto.lt)

 // shoow(touchedByRandDir,)
 //shoow(sloplt,level,twoLt,dopp,se,grad3,grad6)
bugif(twoLt&deefE) //marche
 //bugif(deefE) //marche
 //val (lt,eq)= Grad.slopeLt(prioRand)
 show(prioRand,toto.eq,toto.lt,toto.gt);
} //root classe compilable

