package progOfStaticAgent

import compiler.AST.Delayed
import compiler.ASTBfun.andRedop
import compiler.ASTL.{delayedL, transfer}
import compiler.ASTLfun.{f, reduce}
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.{BoolE, BoolF}
import compiler.{ASTLt, B, E, F, V}
import dataStruc.{BranchNamed, Named}
import progOfmacros.Wrapper.exist
import sdn._
import sdntool.DistT
import sdn.MuStruct.allMuStruct

/**combines flies with the computation of distance, adds a constraints of slowliness
  */
class FliesDist() extends LDAG with Named with BranchNamed
{ val part=new Flies() with DistT;
  part.shoow(part.d.muis) //necessaire pour la reachabilité
  part.showConstraint
}
