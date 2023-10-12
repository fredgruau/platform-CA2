package progOfCA

import compiler.AST.Layer
import compiler.ASTL.inc
import compiler.{AST, ASTLt, SI, V}

/** produce a global uniform field cycling through the 2^nbit values */
class Cycle() extends Layer[(V, SI)](3, "0") with ASTLt[V, SI] {
  override val next: AST[(V, SI)] = inc(this);
  show(this)
}

