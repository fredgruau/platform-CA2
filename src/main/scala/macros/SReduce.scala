package macros

import compiler.AST._
import compiler.ASTL._
import compiler.{B, E, F, V}

/** Contains elementary loops doing simple reduction combined with a broacast from VEF to VEF */
object SReduce {

  /** From a boolV, computes edges on the frontier of blob radius 1 */
  val existE2VDef: Fundef1[(E, B), (V, B)] = {
    val e = p[E, B]("edge")
    val existV: BoolV = orR(transfer(v(e)))
    existV.setName("existV");
    Fundef1("existE2V", existV, e)
  }

  /** wrapper to  Call frontierE.  */
  def existE2V(e: BoolE): BoolV = new Call1(existE2VDef, e) with BoolV


  /** From a boolV, computes edges on the frontier of blob radius 1 */
  val frontierEDef: Fundef1[(V, B), (E, B)] = {
    val b = p[V, B]("blooob")
    val frontierE: BoolE = xorR(transfer(e(b)))
    frontierE.setName("frontierE");
    Fundef1("frontierE", frontierE, b)
  }

  /** wrapper to  Call frontierE.  */
  def frontierE(b: BoolV): BoolE = new Call1(frontierEDef, b) with BoolE


  /** From the frontierE, computes vertices  on the frontier of blob, radius 2 */
  val frontierVDef: Fundef1[(E, B), (V, B)] = {
    val b = p[E, B]("blolob")
    val frontierV: BoolV = orR(transfer(v(b)))
    frontierV.setName("frontierV");
    Fundef1("frontierV", frontierV, b)
  }

  /** wrapper to  Call frontierE.  */
  def frontierV(b: BoolE): BoolV = new Call1(frontierVDef, b) with BoolV

  /** From a boolV, computes edges frontier blob radius 1 */

  /** Computes edge inside the blob, radius 1 */
  val insideEDef: Fundef1[(V, B), (E, B)] = {
    val b = p[V, B]("bloubb")
    val insideE: BoolE = andR(transfer(e(b)))
    insideE.setName("insideE");
    Fundef1("insideE", insideE, b)
  }

  /** wrapper to  Call insideE.  */
  def insideE(b: BoolV): BoolE = new Call1(insideEDef, b) with BoolE


  /** Computes edge inside a rhombus, radius 2 */
  val insideErhombusDef: Fundef1[(V, B), (E, B)] = {
    val b = p[V, B]("input2rhombus")
    val insideE: BoolE = andR(transfer(e(andR(transfer(f(b))))))
    insideE.setName("insideErhombus");
    Fundef1("insideErhombus", insideE, b)
  }

  /** wrapper to  Call insideE.  */
  def insideErhombus(b: BoolV): BoolE = new Call1(insideErhombusDef, b) with BoolE


  /** Computes edge inside a rhombus", radius 2 */
  val insideErhombusEDef: Fundef1[(E, B), (E, B)] = {
    val b = p[E, B]("input2rhombusE")
    val insideE: BoolE = andR(transfer(e(andR(transfer(f(b))))))
    insideE.setName("insideErhombusE");
    Fundef1("insideErhombusE", insideE, b)
  }

  /** wrapper to  Call insideE.  */
  def insideErhombusE(b: BoolE): BoolE = new Call1(insideErhombusEDef, b) with BoolE


  /** Computes faces inside the blob, radius 1 */
  val insideFDef: Fundef1[(V, B), (F, B)] = {
    val b = p[V, B]("blob")
    val insideF: BoolF = andR(transfer(f(b)))
    insideF.setName("insideF");
    Fundef1("insideF", insideF, b)
  }

  /** wrapper to  Call insideE.  */
  def insideF(b: BoolV): BoolF = new Call1(insideFDef, b) with BoolF


  /** From a boolV, computes the neighborhoodV radius 2 */
  val neighborhoodDef: Fundef1[(V, B), (V, B)] = {
    val b = p[V, B]("blob")
    val neighbor: BoolV = orR(transfer(v(orR(transfer(e(b))))))
    neighbor.setName("neighbor");
    Fundef1("neighborhood", neighbor, b)
  }

  /** wrapper to  Call neighborhood.  */
  def neighborhood(b: BoolV): BoolV = new Call1(neighborhoodDef, b) with BoolV


}
