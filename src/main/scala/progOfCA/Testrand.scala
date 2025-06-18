package progOfCA

import compiler.AST.Layer
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.BoolV
import compiler.{AST, ASTLt, B, V}
import dataStruc.{BranchNamed, Named}
import progOfmacros.Util.{randNext, torusify}

/** a single layer works as a program to be simulated
 * This CA tests the computation of distances, but also uses blob on Ev lines, in order to compute gabriel centers.
 * */
class   Testrand() extends Layer[(V,B)](1, "random") with ASTLt[V, B]    with BranchNamed  with Named{
  override val next : BoolV =  randNext(torusify(this))
  show(this)
} //root classe compilable


