package progOfCA

import compiler.ASTLfun.b2SIL
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.{BoolEv, UintV}
import compiler.{ASTLt, B, SI, V}
import dataStruc.BranchNamed
import progOfmacros.Grad
import sdn.Rand
import sdn.Util.randUintV

class   Testlt() extends ConstLayer[V, B](1, "global")  with BranchNamed{
 // val rand1 = new Rand();  val rand2 = new Rand()
  val prioRand: UintV = randUintV(1) //rand1::rand2
 //val (lt,level) = Grad.slopeLt(prioRand)
 val lt= Grad.lt(prioRand)
 show(prioRand,lt);
} //root classe compilable

