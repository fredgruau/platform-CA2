package dataStruc

import scala.collection.immutable
import scala.collection.immutable.HashMap

/** Explicitely stores  neighbors uses names to set them */
trait WiredInOut[T <: WiredInOut[T]] extends DagNode[T] {
  /** to be set if we want to use the Dag feature. */
  var outputNeighbors: List[T] = List.empty;
  /** to be set if we want to use the Dag feature. */
  var inputNeighbors: List[T] = List.empty;

  /** names of variables read by instruction. */
  def usedVars(): immutable.HashSet[String]

  /** names of variables produced by instruction. */
  def names: List[String]

  def isShift = (names.nonEmpty) && names(0).startsWith("shift")

}

object WiredInOut {
  /**
   *
   * @param instrs list of instructions
   * @tparam T the type of the instructions
   * @return mapping each variable to the instructions which define that variable
   */
  def defby[T <: DagNode[T] with WiredInOut[T]](instrs: List[T]): HashMap[String, T] =
    immutable.HashMap.empty ++ instrs.flatMap(a => a.names.map(_ -> a))


  /**
   *
   * @param instrs data to organize into a dag, using strings.
   *               it needs not be instructions
   *               only names and usedVar need to be defined
   * @tparam T
   * Compute inputNeighbor which defines a  Dag of instructions,
   * an input neighbor is an affectation which set a used variable
   * exept for an instruction of the form shifttoto=toto
   * which will be input neighbor to the instructionn defining toto
   * toto will be included in shifttoto's used var
   * it will be appearently scheduled later but in fact not because
   * ending up having a higher priority, let it be scheduled earlier
   * due to the specifics of our scheduling algorithm
   * * */

  def setInputNeighbor[T <: DagNode[T] with WiredInOut[T]](instrs: List[T]) = {
    val defs = defby(instrs)
    for (instr <- instrs) {
      var usedVars = instr.usedVars()
      instr.inputNeighbors = List.empty[T] ++ usedVars.filter(defs.contains(_)).map(defs(_))
    }
  }

  def setOutputNeighbors[T <: DagNode[T] with WiredInOut[T]](instrs: List[T]) = {
    for (a <- instrs)
      for (b <- a.inputNeighbors)
        b.outputNeighbors = a :: b.outputNeighbors;
  }

  def setInputAndOutputNeighbor[T <: DagNode[T] with WiredInOut[T]](instrs: List[T]) = {
    setInputNeighbor(instrs)
    setOutputNeighbors(instrs)
  }
}