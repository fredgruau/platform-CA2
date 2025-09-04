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
import sdntool.{DistGcenter, DistT, gCenter}
import sdn.MuStruct.allMuStruct

/**combines flies with the computation of distance to gabriel centers, it needs 5 bits to be continuous,
 * todo: see if adding a constraints of slowliness could shift from having 5 bits to 4 bits
  */
class FliesDist() extends LDAG with Named with BranchNamed
{ val part=new Flies() with DistT with gCenter with DistGcenter;
  part.shoow(part.d.muis) //necessaire pour la reachabilité
  part.showConstraint
  part.shoow(part.gCenterV,part.gCenterE)
  part.shoow(part.dg.muis.pred)
}
