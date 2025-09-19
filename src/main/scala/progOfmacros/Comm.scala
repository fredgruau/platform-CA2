package progOfmacros

import compiler.SpatialType._
import compiler.AST._
import compiler.ASTL._
import compiler.ASTLfun.e
import compiler._
import progOfmacros.Wrapper.exist
/** contains communication primitives using rotations and symmetries
 *  initially most code are indeed macros, but then we add code that uses those macro
 *  such as adjacentRing, adjacentBall which uses neighborsSym
 *  we do not definie macros for those, in order to avoid generating too much java*/
object Comm {
  /** Unary function: From a boolVe computes another symetric boolVe, exploiting the sym operator on edges */
  val neighborsDef: Fundef1[(T[V, E], B), (T[V, E], B)] = {
    val ve = pL[T[V,E], B]("ngh")
    val ver: BoolVe = transfer(sym(transfer(ve)))
    ver.setName("ver");
    Fundef1("comm.neighbors", ver, ve)
  }
  /** wrapper   */
  def neighborsSym(ve: BoolVe): BoolVe = new Call1[(T[V,E], B), (T[V, E], B)](neighborsDef, ve) with BoolVe

  def adjacentRing(bv: BoolV):BoolV=exist(neighborsSym(e(bv)))
  def adjacentBall(bv: BoolV):BoolV=adjacentRing(bv)|bv

  val neighborsDefUI: Fundef1[(T[V, E], UI), (T[V, E], UI)] = {
    val ve = pL[T[V,E],UI]("ngh")
    val ver: UintVe = transfer(sym(transfer(ve)))
    ver.setName("ver");
    Fundef1("comm.neighborsUI", ver, ve)
  }


  def neighborsSymUI(ve: UintVe): UintVe = new Call1[(T[V,E], UI), (T[V, E], UI)](neighborsDefUI, ve) with UintVe

  /** From a boolfE, computes the appex vertices boolfV */
  val apexVDef: Fundef1[(T[E, F], B), (T[V, F], B)] = {
    val ef = pL[T[E, F], B]("distantEdgevf")
    val apexVf: BoolVf = transfer(sym(transfer(ef)))
    apexVf.setName("apexVf");
    Fundef1("comm.apexEtoV", apexVf, ef)
  }
  /** wrapper .  */
  def apexV(ef: BoolEf): BoolVf = new Call1[(T[E, F], B), (T[V, F], B)](apexVDef, ef) with BoolVf



  /** From a boolfV, computes the appex vertices boolfE */
  val apexEDef: Fundef1[(T[V, F], B), (T[E, F], B)] = {
    val ef = pL[T[V, F], B]("distantEdgeef")
    val apexEf: BoolEf = transfer(sym(transfer(ef)))
    apexEf.setName("apexEf");
    Fundef1("comm.apexVtoE", apexEf, ef)
  }
  /** wrapper .  */
  def apexE(ef: BoolVf): BoolEf = new Call1[(T[V, F], B), (T[E, F], B)](apexEDef, ef) with BoolEf


  val apexEuiDef: Fundef1[(T[V, F], UI), (T[E, F],UI)] = {
    val ef = pL[T[V, F],UI]("distantEdgeef")
    val apexEf: UintEf = transfer(sym(transfer(ef)))
    apexEf.setName("apexEf");
    Fundef1("comm.apexEtoVui", apexEf, ef)
  }

  /** wrapper .  */
  def apexEui(ef: UintVf): UintEf = new Call1[(T[V, F], UI), (T[E, F],UI)](apexEuiDef, ef) with UintEf
  /** From a boolfV, computes the appex vertices boolfE */


  /** symetrie Ev=>Ev */
  val symEvDef: Fundef1[(T[E, V], B), (T[E, V], B)] = {val ev = pL[T[E, V], B]("ev");  Fundef1("comm.symev", sym(ev) ,ev)  }
  def symEv(ev: BoolEv): BoolEv = new Call1[(T[E, V], B),(T[E, V], B)](symEvDef, ev) with BoolEv
  val symEfDef: Fundef1[(T[E, F], B), (T[E, F], B)] = {val ev = pL[T[E, F], B]("ev");  Fundef1("comm.symev", sym(ev) ,ev)  }
  def symEf(ev: BoolEf): BoolEf = new Call1[(T[E, F], B),(T[E, F], B)](symEfDef, ev) with BoolEf

  def apexVnoMacro(ef: BoolEf): BoolVf = transfer(sym(transfer(ef))) //pour tester le calcul du rayon avec une non augmentation


}
