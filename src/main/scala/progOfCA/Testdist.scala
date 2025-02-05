package progOfCA

import compiler.AST.Layer
import compiler.ASTL._
import compiler.ASTLfun.orR
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.BoolV
import compiler.{AST, B, V}
import dataStruc.{BranchNamed, Named}
import progOfmacros.Wrapper.borderS
import sdn.Util.{addBlobE, safeGrow}

import java.util
import scala.collection.immutable.HashMap

/** a single layer works as a program to be simulated */
class   Testdist() extends ConstLayer[V, B](1, "global") with BranchNamed  with Named{
  val src=new Testdist2()
  show(src.d);
} //root classe compilable
/** a single layer works as a program to be simulated */
class   Testdist2() extends ConstLayer[V, B](1, "global") with BranchNamed with Named with DistT {
} //root classe compilable


