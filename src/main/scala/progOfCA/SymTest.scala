package progOfCA

import compiler.ASTL.{sym, transfer}
import compiler.ASTLt.ConstLayer
import compiler.SpatialType._
import compiler._
import progOfmacros.RedSwrapper.exist

/** sert a tester les fonction utilisant les type T[X,Y] via les operations transfer et sym */
class SymTest extends ConstLayer[E, B](1, "global") with BoolE {
  val emptyRhomb1: BoolF = exist[E, F](this)
  // val eftofe = transfer(this)
  // val fvtovF = transfer(this)
  //val apx:BoolVf=sym(this)
  //val nouv:IntV = this + maxSI()
  //val nouv:IntV=min(this,0)
  //show (nouv)
  show(this, emptyRhomb1)
}