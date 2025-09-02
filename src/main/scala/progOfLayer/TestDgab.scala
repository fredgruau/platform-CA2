package progOfLayer

import compiler.ASTLt.ConstLayer
import compiler.{ASTLt, B, V}
import dataStruc.{BranchNamed, Named}
import progOfStaticAgent.Flies
import sdn._
import sdntool.{DistGcenter, DistT, gCenter}

/** same, but avoioding the wrapping of a constlayer */
class TestDgab() extends LDAG with Named with BranchNamed {
  val constPart = new MuStruct[V, B] with muEmptyBag with BranchNamed with DistT with gCenter with DistGcenter{
    /** support of agent */
    override val muis = new ConstLayer[V, B](1, "global") with Stratify[V, B] with ASTLt[V, B] with carrySysInstr
    shoow(muis,d.muis)
    shoow(gCenterE,gCenterV,dg.muis.pred)
  } //root classe compilable

}



