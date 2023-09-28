package progOfmacros

import compiler.AST.{p, _}
import compiler.ASTL.{v, _}
import compiler.repr.nomV
import compiler.{B, E, F, V}
import progOfmacros.RedS.{exist}
import progOfmacros.SReduce.existF2V

/** Contains elementary loops doing simple reduction combined with a broacast from VEF to VEF */
object SReduce {

  /** From a boolE, computes adjacent vertices */
  val existE2VDef: Fundef1[(E, B), (V, B)] = {
    val e = p[E, B]("edge")
    val existV: BoolV = orRdef(transfer(v(e)))
    existV.setName("existV");
    Fundef1("reds.existE2V", existV, e) //will be stored as a static function "existE2V_1" of reds javafile
  }


  /** wrapper to  Call existE2V. */
  def existE2V(e: BoolE): BoolV = new Call1(existE2VDef, e) with BoolV


  /** From a boolE, computes adjacent vertices */
  val insideE2VDef: Fundef1[(E, B), (V, B)] = {
    val e = p[E, B]("edge")
    val insideV: BoolV = andRdef(transfer(v(e)))
    insideV.setName("insideV");
    Fundef1("insideE2V", insideV, e)
  }
  def insideE2V(e: BoolE): BoolV = new Call1(insideE2VDef, e) with BoolV


  /** From a boolE, computes adjacent vertices */
  val existE2FDef: Fundef1[(E, B), (F, B)] = {
    val e = p[E, B]("edge")
    val existF: BoolF = orR(transfer(f(e)))
    existF.setName("existF");
    Fundef1("existE2F", existF, e)
  }

  /** wrapper to  Call existE2V. */
  def existE2F(e: BoolE): BoolF = new Call1(existE2FDef, e) with BoolF


  /** From a boolE, computes adjacent vertices */
  val existF2VDef: Fundef1[(F, B), (V, B)] = {
    val f = p[F, B]("face")
    val existV: BoolV = orR(transfer(v(f)))
    existV.setName("existV");
    Fundef1("existE2F", existV, f)
  }

  /** wrapper to  Call existE2V. */
  def existF2V(f: BoolF): BoolV = new Call1(existF2VDef, f) with BoolV

  /** From a boolV, computes adjacent edges */
  val existV2EDef: Fundef1[(V, B), (E, B)] = {
    val v = p[V, B]("vertice")
    val existE: BoolE = orR(transfer(e(v))) //pas besoin de defEv
    existE.setName("existE");
    Fundef1("reds.existV2E", existE, v)
  }

  /** wrapper to  Call existV2E. */
  def existV2E(v: BoolV): BoolE = new Call1(existV2EDef, v) with BoolE


  /** From a boolV, computes adjacent edges */
  val existF2EDef: Fundef1[(F, B), (E, B)] = {
    val f = p[F, B]("face")
    val existE: BoolE = orR(transfer(e(f)))
    existE.setName("exsistE");
    Fundef1("existF2E", existE, f)
  }

  /** wrapper to  Call existV2E. */
  def existF2E(f: BoolF): BoolE = new Call1(existF2EDef, f) with BoolE


  /** From a boolV, computes adjacent faces */
  val existV2FDef: Fundef1[(V, B), (F, B)] = {
    val v = p[V, B]("vertice")
    val existF: BoolF = orR(transfer(f(v)))
    existF.setName("existF");
    Fundef1("existV2F", existF, v)
  }

  /** wrapper to  Call existV2E. */
  def existV2F(v: BoolV): BoolF = new Call1(existV2FDef, v) with BoolF

  /** wrapper to  Call neighborhood. */
  def neighborhood(b: BoolV): BoolV = new Call1(neighborhoodDef, b) with BoolV

  /** From a boolV, computes the neighborhoodV radius 2 */
  val neighborhoodDef: Fundef1[(V, B), (V, B)] = {
    val b = p[V, B]("blob")
    val neighbEE: BoolE = existV2E(b)

    val neighbor1: BoolV = exist(neighbEE)
    // val neighbor2: BoolV = inside(neighbEE)
    val neighbor = neighbor1 //| neighbor2
    neighbor.setName("neighbVV");
    Fundef1("neighborhood", neighbor, b)
  }


  /** From a boolF, computes the neighborhoodF radius 2 by going through edges */
  val neighborhoodfDef: Fundef1[(V, B), (V, B)] = {
    val b = p[V, B]("blob")
    val neighbFF = existV2F(b)
    val neighbor: BoolV = existF2V(neighbFF)
    neighbor.setName("neighbVV");
    Fundef1("neighborhood", neighbor, b)
  }

  /** wrapper to  Call neighborhood. */
  def neighborhoodf(b: BoolV): BoolV = new Call1(neighborhoodfDef, b) with BoolV

  /** From a boolV, computes the neighborhoodV radius 2 by going through faces */
  val neighborhoodfeDef: Fundef1[(F, B), (F, B)] = {
    val f = p[F, B]("face")
    val neighbE = existF2E(f)
    val neighbor: BoolF = existE2F(neighbE)
    neighbor.setName("neighbVV");
    Fundef1("neighborhood", neighbor, f)
  }

  /** wrapper to  Call neighborhood. */
  def neighborhoodfe(b: BoolF): BoolF = new Call1(neighborhoodfeDef, b) with BoolF


  /** From a boolV, computes edges on the frontier of blob radius 1 */
  val frontierEDef: Fundef1[(V, B), (E, B)] = {
    val b = p[V, B]("blooob")
    val frontierE: BoolE = xorR(transfer(e(b)))
    frontierE.setName("frontierE");
    Fundef1("frontierE", frontierE, b)
  }

  /** wrapper to  Call frontierE. */
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



}
