package progOfmacros

import compiler.SpatialType._
import compiler.AST._
import compiler.ASTL._
import compiler._

object Comm {
  /** From a boolfE, computes the appex vertices boolfV */
  val neighborsDef: Fundef1[(T[V, E], B), (T[V, E], B)] = {
    val ve = pL[T[V,E], B]("ngh")
    val ver: BoolVe = transfer(sym(transfer(ve)))
    ver.setName("ver");
    Fundef1("comm.neighbors", ver, ve)
  }
  /** wrapper   */
  def neighborsSym(ve: BoolVe): BoolVe = new Call1[(T[V,E], B), (T[V, E], B)](neighborsDef, ve) with BoolVe

  /** From a boolfE, computes the appex vertices boolfV */
  val apexVDef: Fundef1[(T[E, F], B), (T[V, F], B)] = {
    val vf = pL[T[E, F], B]("distantEdgevf")
    val apexVf: BoolVf = transfer(sym(transfer(vf)))
    apexVf.setName("apexVf");
    Fundef1("comm.apexEtoV", apexVf, vf)
  }

  /** wrapper .  */
  def apexV(ef: BoolEf): BoolVf = new Call1[(T[E, F], B), (T[V, F], B)](apexVDef, ef) with BoolVf

  /** From a boolfV, computes the appex vertices boolfE */
  val apexEDef: Fundef1[(T[V, F], B), (T[E, F], B)] = {
    val ef = pL[T[V, F], B]("distantEdgeef")
    val apexEf: BoolEf = transfer(sym(transfer(ef)))
    apexEf.setName("apexEf");
    Fundef1("comm.apexEtoV", apexEf, ef)
  }

  /** wrapper .  */
  def apexE(ef: BoolVf): BoolEf = new Call1[(T[V, F], B), (T[E, F], B)](apexEDef, ef) with BoolEf



  def apexVnoMacro(ef: BoolEf): BoolVf = transfer(sym(transfer(ef))) //pour tester le calcul du rayon avec une non augmentation


}
