package progOfCA

import compiler.AST.Layer
import compiler.ASTL._
import compiler.ASTLfun.{orR, toNeighb}
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.BoolV
import compiler.{AST, B, V}
import progOfCA.Force.qpointRand

import java.util
import scala.collection.immutable.HashMap

class Testdist() extends ConstLayer[V, B](1, "global") with DistT {
  show(this)
} //root classe compilable

