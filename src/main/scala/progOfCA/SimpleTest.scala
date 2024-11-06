package progOfCA

import compiler.ASTB.Uint
import compiler.ASTL.{sym, transfer}
import compiler.ASTLfun._
import compiler.ASTLt.ConstLayer
import compiler.SpatialType._
import compiler._
import progOfmacros.Wrapper.existS
import progOfmacros.RedT.{enlarge, enlargeEF, enlargeFE}

/** sert a tester les fonction utilisant les type T[X,Y] via les operations transfer et sym */
class SimpleTest extends ConstLayer[V, UI](3, "global") with UintV {
  val test0 = transfer(e(this))
  //val test1:BoolVe=enlargeFE(test0)
  // val test2=orR(transfer(test1))
  //val emptyRhomb1: BoolF = exist[E, F](this)
  // val eftofe = transfer(this)
  // val fvtovF = transfer(this)
  //val apx:BoolVf=sym(this)
  //val nouv:IntV = this + maxSI()
  //val nouv:IntV=min(this,0)
  //show (nouv)
  show(this, test0)
}