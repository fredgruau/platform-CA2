package progOfmacros

import compiler.AST._
import compiler.ASTL._
import compiler._

object Comm {
  /** From a boolfE, computes the appex vertices boolfV */
  val apexVDef: Fundef1[(T[E, F], B), (T[V, F], B)] = {
    val ef = p[T[E, F], B]("distantEdge")
    val apexV: BoolfV = transfer(sym(transfer(ef)))
    apexV.setName("apexV");
    Fundef1("apexEtoV", apexV, ef)
  }

  /** wrapper to  Call frontierE.  */
  def apexV(ef: BoolfE): BoolfV = new Call1(apexVDef, ef) with BoolfV

  def apexVnoMacro(ef: BoolfE): BoolfV = transfer(sym(transfer(ef))) //pour tester le calcul du rayon avec une non augmentation


}
