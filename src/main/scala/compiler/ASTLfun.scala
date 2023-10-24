package compiler

import compiler.AST.Fundef2
import compiler.ASTL.{IntEv, IntVe, sym, transfer, e}

/** contains generic primitive manipulating ASTLs, without direct access to the constructors */
object ASTLfun {
  /** a vertex field get on its six edge, the six neighbor values, so that it can then reduce them. */
  def neighbors[R <: Ring](arg: ASTLt[V, R])(implicit n: repr[R]): ASTLt[T[V, E], R] = {
    val meVois: ASTLt[T[E, V], R] = transfer(e(arg))
    val symed: ASTLt[T[E, V], R] = sym(meVois)
    transfer(symed)
  }

}

