package progOfCA

import compiler.ASTLfun.b2SIL
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.{BoolEv, UintV}
import compiler.{ASTLt, B, SI, V}
import dataStruc.BranchNamed
import progOfmacros.Grad
import sdn.Rand
import sdn.Util.{addLt, randUintV}
/** tests the lt macro, containts a bugif */
class   Testlt() extends ConstLayer[V, B](1, "global")  with BranchNamed{
 // val rand1 = new Rand();  val rand2 = new Rand()
  val prioRand = randUintV(6) //rand1::rand2
  val toto=addLt(prioRand)
 //val (lt,eq)= Grad.slopeLt(prioRand)
 show(prioRand,toto.diff,toto.eq,toto.lt,toto.gt);
} //root classe compilable

