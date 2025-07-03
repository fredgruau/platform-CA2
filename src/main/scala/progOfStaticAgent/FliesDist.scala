package progOfStaticAgent

import compiler.AST.Delayed
import compiler.ASTBfun.andRedop
import compiler.ASTLfun.reduce
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.BoolE
import compiler.{B, E}
import dataStruc.{BranchNamed, Named}
import sdn._
import sdntool.{DistT, Distmu}
import sdn.MuStruct.allMuStruct

/**
 * contains just a flies plus a mustruct distance to it
  */
class FliesDist() extends LDAG with Named with BranchNamed
{  val part=new Flies() with DistT;
  //val d=new Distmu(part,3)
  val s=compiler.ASTL.delayedL(part.d.muis.pred)
  part.shoow(s,part.d.delta,part.d.gap, part.d.sloplt, part.d.level)


   // on bosse sur le LDAG
/*   val nongenerators=allMuStruct.map(_.inputNeighbors.toSet).reduce(_ union _)
   val generators=allMuStruct -- nongenerators
   print(generators)*/

   //on peut construire le DAG si on veut.
}
