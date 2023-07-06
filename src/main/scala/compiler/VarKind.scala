package compiler

import VarKind._

sealed class VarKind extends Comparable[VarKind] {
  def compareTo(t: VarKind): Int = vkMap(this) - vkMap(t)

  /** @return True if field needs to be stored in CA memory  */
  def needStored: Boolean = this match {
    case ParamD() | ParamR() | ParamRR(_) | StoredField() | LayerField(_) //|ParamDR()
    => true;
    case _ => false
  }

  def isParamR = this match {
    case ParamR() | ParamRR(_) => true
    case _ => false
  }

  def isParam = this match {
    case ParamR() | ParamRR(_) | ParamD() => true
    case _ => false
  }

  //def isParam = isInstanceOf[ParamRR] || isInstanceOf[ParamD] || isInstanceOf[ParamR]
  def isRadius1: Boolean = this match {
    case ParamRR(1) => true
    case _ => false
  }

  def isStoredField: Boolean = this match {
    case StoredField() => true;
    case _ => false
  }

  def isLayerField: Boolean = this match {
    case LayerField(_) => true;
    case _ => false
  }
}

object VarKind {
  val vkMap: Map[VarKind, Int] = Map(ParamD() -> 1, ParamR() -> 2, ParamRR(0) -> 3, ParamRR(1) -> 4,
    ParamRR(2) -> 5, ParamRR(3) -> 6, MacroField() -> 9, StoredField() -> 10,
    LayerField(1) -> 11, LayerField(2) -> 12, LayerField(3) -> 13, LayerField(4) -> 14)

  /** Default type of variable which will not be stored in the CA memory,
   * instead, it will be temporarily hold in a java longint register.
   * Used to compute liveness at the beginning and at the end of the loop body */
  final case class MacroField() extends VarKind {}

  /** used only at the very beginning, when constructing the Dag */
  final case class LayerField(nb: Int) extends VarKind

  /** used when a Param AST node is replaced by a Read */
  final case class ParamD() extends VarKind

  /** fields which are returned by a macro, */
  final case class ParamR() extends VarKind

  /** fields which are returned by a macro, with the radius included (we need to know the radius only for those, ) */
  final case class ParamRR(radius: Int) extends VarKind

  /** the famous data-result param. It could be used in the specific case when a layer is passed and updated by the same macro,
   * we will treat them in the ultimate code generation phase, by not passing the result parameter when calling,
   * and removing it from the list of result parameters when defining the function. Not used for the moment being */
  // final case class ParamDR() extends VarKind

  /** For non macro loop, stored Field are local CA layers to be passed as result parameters */
  final case class StoredField() extends VarKind

  /** usable only in elementary macro to be compiled in loops */
  final case class Timetminus1(name: String) extends VarKind

}
