package progOfCA

import compiler.ASTL.{sym, transfer}
import compiler.ASTLt.ConstLayer
import compiler.SpatialType._
import compiler._

/** sert a tester les fonction utilisant les type T[X,Y] via les operations transfer et sym */
class SymTest extends ConstLayer[T[F, V], B](1, "global") with BoolFv {
  val fvtovF = transfer(this)
  //val apx:BoolVf=sym(this)
  //val nouv:IntV = this + maxSI()
  //val nouv:IntV=min(this,0)
  //show (nouv)
  show(this, fvtovF)
}