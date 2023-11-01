package progOfmacros

import compiler.SpatialType._
import compiler.AST._
import compiler.ASTL._
import compiler._

object Comm {
  /** From a boolfE, computes the appex vertices boolfV */
  val apexVDef: Fundef1[(T[E, F], B), (T[V, F], B)] = {
    val ef = p[T[E, F], B]("distantEdge")
    val apexV: BoolVf = transfer(sym(transfer(ef)))
    apexV.setName("apexV");
    Fundef1("apexEtoV", apexV, ef)
  }

  /** wrapper to  Call frontierE.  */
  def apexV(ef: BoolEf): BoolVf = new Call1(apexVDef, ef) with BoolVf

  def apexVnoMacro(ef: BoolEf): BoolVf = transfer(sym(transfer(ef))) //pour tester le calcul du rayon avec une non augmentation


}
