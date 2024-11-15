package progOfCA

import compiler.ASTLfun.b2SIL
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.BoolEv
import compiler.{ASTLt, B, SI, V}
import dataStruc.BranchNamed
import progOfmacros.Grad
import sdn.Rand

class   Testlt() extends ConstLayer[V, B](1, "global")  with BranchNamed{
  val _rand1 = new Rand()
  val prioRand: ASTLt[V, SI] =b2SIL(_rand1)
  val (lt,level) = Grad.slopeLt(prioRand)
  show(this,prioRand,lt,level);
} //root classe compilable

