package compiler

package compiler

/** *
 * Regroup all the information necessary to compile one integer instructions.
 * allows to display this info for val loops:List[Loop]a last readable check, and to apply the last simplifications
 */
class Looop(loc: Option[Locus], instr: Instr) {

  override def toString: String = {
    instr.toString(DataProg.nbSpace(loc))
  }
}
