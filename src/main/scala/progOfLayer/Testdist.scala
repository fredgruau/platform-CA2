package progOfLayer

import compiler.AST.Layer
import compiler.ASTL._
import compiler.ASTLfun.orR
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.BoolV
import compiler.{AST, B, V}
import dataStruc.{BranchNamed, Named}
import sdntool.DistT
import progOfmacros.Wrapper.borderS
import sdn.Stratify
import sdn.Util.{addBlobE, safeGrow}

import java.util
import scala.collection.immutable.HashMap

/** a single layer works as a program to be simulated
 * This CA tests the computation of distances, but also uses blob on Ev lines, in order to compute gabriel centers.
 * */
class   Testdistt() extends ConstLayer[V, B](1, "global") with BranchNamed  with Named{
  val src=new Testdistt()
  //show(src.d);
} //root classe compilable

/** same, but avoioding the wrapping of a constlayer */
/*
class   Testdist() extends ConstLayer[V, B](1, "global")
  with Stratify[V,B] with BranchNamed with Named with DistT {
  show(d,this)
} //root classe compilable

*/

