package progOfLayer

import compiler.AST.Layer
import compiler.ASTL._
import compiler.ASTLfun.orR
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.BoolV
import compiler.{AST, ASTLt, B, Locus, Ring, V}
import dataStruc.DagNode.EmptyBag
import dataStruc.{BranchNamed, Named}
import sdntool.addDist
import progOfmacros.Wrapper.borderS
import sdn.{LDAG, MuStruct, Stratify, carrySysInstr, muEmptyBag}
import sdn.Util.safeGrow

import java.util
import scala.collection.immutable.HashMap

/** a single layer works as a program to be simulated
 * This CA tests the computation of distances, but also uses blob on Ev lines, in order to compute gabriel centers.
 * */
/*class   Testdistt() extends ConstLayer[V, B](1, "global") with BranchNamed  with Named{
  val src=new Testdistt()
  //show(src.d);
} */

/** same, but avoioding the wrapping of a constlayer */
class Testdist() extends LDAG with Named with BranchNamed {
  val constPart = new MuStruct[V, B] with muEmptyBag with BranchNamed with addDist {
    /** support of agent */
    override val muis = new ConstLayer[V, B](1, "global") with Stratify[V, B] with ASTLt[V, B] with carrySysInstr
    shoow(muis,d.muis)
  } //root classe compilable

}

//class   Testdist2() extends ConstLayer[V, B](1, "global") with BranchNamed with Named with DistT {show(d,this)} //root classe compilable


