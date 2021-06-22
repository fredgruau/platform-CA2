package compiler

import compiler.VarKind._

sealed class VarKind {
  def needStored: Boolean = this match {
    case DisplayField(_, _) | BugifField(_) | LayerField(_) | ParamD() | ParamR() | ParamDR() | StoredField()
    => true;
    case _ => false
  }

  def notInMacro: Boolean = this match {
    case DisplayField(_, _) | BugifField(_) | StoredField() //TODO sortir display, bugif fields.
    => true;
    case _ => false
  }

  def isStoredField: Boolean = this match {
    case StoredField() => true;
    case _ => false
  }

  /** True if variable is live before each loop iteration. */
  def isInput: Boolean = this match {
    case LayerField(_) | ParamD() => true;
    case _ => false
  }

  /** True if variable is live after each loop iteration. */
  def isOutput: Boolean = this match {
    case LayerField(_) | ParamR() | DisplayField(_, _) | BugifField(_) => true;
    case _ => false
  }

  /** True for variable that needs to be computed, (and will not be used by others? */
  //TODO its just ParamR, now
  def needCompute: Boolean = this match {
    case LayerField(_) | ParamR() | DisplayField(_, false) | BugifField(_) => true;
    case _ => false
  }

  def isLayer: Boolean = this match {
    case LayerField(_) => true;
    case _ => false
  }
}

// we must add a field stop for all variable, if stop is true  execution   stops after computation of the variable,
// stop is set to true for all the field of a new macro we would like to test, using a system call.
object VarKind {
  /**Used to compute liveness at the beginning and at the end of the loop body  */
  final case class Field() extends VarKind

  /** probably deprecated */
  final case class LayerField(nb:Int) extends VarKind

  /** used to replace a Param AST node by a Read */
  final case class ParamD() extends VarKind
  final case class ParamR() extends VarKind
  /**the famous data-result param. It is used in the specific case when a layer is passed and updated by the same macro, 
   * we will treat them in the ultimate code generation phase, by not passing the result parameter when calling,
   * and removing it from the list of result parameters when defining the function. */
  final case class ParamDR() extends VarKind

  /** stored is necessary for a variable created to be passed as a resultParameter to procedure.  */
   final case class StoredField() extends VarKind 
  /**   if usefull, variables is computed even if not displayed*/
  final case class DisplayField(name: String, usefull: Boolean) extends VarKind
  final case class BugifField(name: String) extends VarKind
  /**usable only in elementary macro to be compiled in loops */
  final case class Timetminus1(name: String) extends VarKind
}
