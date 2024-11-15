package progOfCA

import compiler.AST.Layer
import compiler.ASTL._
import compiler.ASTLfun.orR
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.BoolV
import compiler.{AST, B, V}
import dataStruc.BranchNamed

import java.util
import scala.collection.immutable.HashMap

/** a single layer works as a program to be simulated */
class   Testdist() extends ConstLayer[V, B](1, "global") with DistT with BranchNamed{
  show(this);
} //root classe compilable

