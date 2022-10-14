package dataStruc

import compiler.Circuit.iTabSymb

import scala.collection.{immutable, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.mutable.ArrayBuffer

/** Explicitely stores  neighbors uses names to set them */
trait WiredInOut[T <: WiredInOut[T]] extends DagNode[T] {
  /** to be set if we want to use the Dag feature. */
  var outputNeighbors: List[T] = List.empty;
  /** to be set if we want to use the Dag feature. */
  var inputNeighbors: List[T] = List.empty;

  /** names of variables read by instruction. */
  def usedVars(): Set[String]

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

  /**
   *
   * @param dagNodes List of Dag's elements
   * @return returns the max element of the list, by filtering  out  elements who  have output Neighbors in the list
   */
  def sup2[T <: WiredInOut[T]](dagNodes: List[T]) = {
    val s = dagNodes.toSet
    dagNodes.filter(_.outputNeighbors.toSet.intersect(s).isEmpty)
  }

  /**
   *
   * @param packets defines and uses variables that need to be stored at some adresses
   * @tparam T
   * @return an Hashmap telling where to store each variables
   */
  def heap[T <: WiredInOut[T]](packets: List[T]): HashMap[String, Int] = {
    /**
     * adress (or register number) where a given variable will be stored,
     */
    var adress: HashMap[String, Int] = HashMap()
    /**
     * heap memory, for each integer adress, stores which variable is stored or wether it is empty
     */
    var memory: ArrayBuffer[String] = //new mutable.ArrayBuffer[String](20) //I minimize the proba that it will not be enough
      mutable.ArrayBuffer.fill(20)(null)

    /**
     * @param valu new variables to be stored in memory
     *             stores variables in memory, updates the mapping res
     */
    def place(valu: Set[String]): Unit = {
      var value = valu
      for (i <- 0 to memory.size - 1) {
        if (value.isEmpty)
          return
        if (memory(i) == null) {
          val e = value.head
          memory(i) = e
          value = value - e
          adress = adress + (e -> i)
        }
      }
      throw new Exception(" we need bigger memory")
    }

    /** remove the variables from memory */
    def unPlace(value: Set[String]) = {
      for (s <- value)
        memory(adress(s)) = null
    }

    /** computes the set of variables live after each packet */
    def livVars: List[HashSet[String]] = {
      var liveVar: HashSet[String] = HashSet() //last liveVar are empty!
      var liveVars: List[HashSet[String]] = List(liveVar) //strings contained in buffer
      for (p <- packets.reverse) { //we compute live vars, starting from the end towards the beginning
        liveVar = liveVar.union(p.usedVars()).diff(p.names.toSet)
        liveVars ::= liveVar
      }
      liveVars
    }

    val liveVars = livVars
    var liveVar = liveVars.head
    place(liveVar)
    for ((p, l) <- (packets zip liveVars.tail)) {
      place(p.names.toSet) //affected variables need a memory
      //here the memory should be passed to f, if there is a call to f
      unPlace(p.names.toSet.union(liveVar).diff(l)) //we now free the previously livevar and the names exepted
      // those which will still live
      liveVar = l
    }


    adress
  }

  /**
   *
   * @param usedVars set of defined variable plus set of read variables, at each loop
   * @return an association of each variable to an integer corresponding to a variable used for arithmetic
   *         the required number  of such cells is simply the map size
   *         The algo follows a generic allocation strategy; reusable in other circumstances.
   *         todo turn this generic
   */
  def allocateInt(usedVars: List[(HashSet[String], HashSet[String])]): iTabSymb[Int] = {
    /**
     * adress (or register number) where a given variable will be stored,
     */
    var res: HashMap[String, Int] = HashMap()
    /**
     * heap memory, for each integer adress, stores which variable is stored or wether it is empty
     */
    var memory: ArrayBuffer[String] = //new mutable.ArrayBuffer[String](20) //I minimize the proba that it will not be enough
      mutable.ArrayBuffer.fill(20)(null)

    var liveVars: HashSet[String] = HashSet() //strings contained in buffer

    /**
     * @param valu new variables to be stored in memory
     *             stores variables in memory, updates the mapping res
     */
    def place(valu: HashSet[String]): Unit = {
      var value = valu
      for (i <- 0 to memory.size - 1) {
        if (value.isEmpty)
          return
        if (memory(i) == null) {
          val e = value.head
          memory(i) = e
          value = value - e
          res = res + (e -> i)
        }
      }
      throw new Exception(" we need bigger memory")
    }

    /** remove the variables from memory */
    def unPlace(value: HashSet[String]) = {
      for (s <- value)
        memory(res(s)) = null
    }

    for ((defined, read) <- usedVars) {
      place(read diff liveVars) //adds new variables defined before, read for the last time
      liveVars = liveVars.union(read)
      place(defined diff liveVars) //newly defined variable d may be still in use after, we have to add them only if it was not the case
      liveVars = liveVars diff defined //newly defined variable will surely not be used before their point of definition
      unPlace(defined)
    }
    res
  }


}