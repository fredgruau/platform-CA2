package dataStruc

import compiler.Circuit.iTabSymb

import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.{immutable, mutable}
import scala.collection.mutable.LinkedHashSet

/**
 * Allows to iterates on the different values taken by the heap, during execution of the instruction of a main loop
 * will also retrieve the adress assigned to variables, upon completion of the iteration.
 *
 * @param packets defines and uses variables that need to be stored at some adresses
 * @param heap    initial state of heap, which stores which variable is stored or wether it is empty
 *                //different adress will be retried for different initial heap
 * @tparam T
 */
class HeapStates[T <: WiredInOut[T]](val packets: List[T], //todo use this class for the mainRoot's adress
                                     var heap: immutable.Vector[String] = Vector(null), //we put one value
                                     val shown: LinkedHashSet[String] = LinkedHashSet()
                                    ) extends Iterable[(Vector[String], iTabSymb[Int])] {
  /** computes the Hashset of variables live after each packet */
  def livVars: List[mutable.LinkedHashSet[String]] = {
    var liveVar: mutable.LinkedHashSet[String] = shown //shown variable are live at the end, because we need to access their state in order to display them
    var liveVars: List[mutable.LinkedHashSet[String]] = List(liveVar) //strings contained in buffer
    for (p <- packets.reverse) { //we compute live vars, starting from the end towards the beginning
      liveVar = liveVar.union(p.usedVars()).diff(p.names.toSet)
      liveVars ::= liveVar
    }
    liveVars
  }

  val liveVars = livVars
  var heapSize = 0
  /**
   * adress (or register number) where a given variable will be stored,
   * an association of each variable to an integer corresponding to a variable used for arithmetic
   * *         the required number  of such cells is simply the map size
   * *         The algo follows a generic allocation strategy; reusable in other circumstances.
   * adress is used  by unplace, which frees memory,
   */
  var adress: HashMap[String, Int] = HashMap()

  /** a given variables should be present a single time */
  def checkSingleOccurence = {
    var nbOcc = new HashSet[String]()
    for (i <- 0 until heap.size)
      if (heap(i) != null) {
        assert(!nbOcc.contains(heap(i)), heap(i) + "alreadyDefined!")
        nbOcc = nbOcc + heap(i)
      }
  }

  /**
   * @param valu new items to be stored in memory
   *             stores variables in memory, updates the mapping res
   */
  def place(valu: LinkedHashSet[String]): Unit = {
    var value = valu
    var i: Int = 0
    while (value.nonEmpty) {
      if (i == heap.size) {
        heap = heap :+ null //we need to extend the memory, we add a cell with a null content
        heapSize += 1
      }
      if (heap(i) == null) { //we found an empty spot to store one of the time in value
        val e = value.head
        heap = heap.updated(i, e)
        //System.out.println("HeapState: "+heap)
        checkSingleOccurence
        value = value - e
        if (!adress.contains(e))
        //  it can easily be the case that several iterations on the heaps are performed; for printing for example
        //  we want to take into account only the first one.
        adress = adress + (e -> i)
      }
      i = i + 1
    }

  }

  /** remove the variables from memory */
  def unPlace(value: Set[String]) = {
    for (s <- value)
      heap = heap.updated(adress(s), null) // a value is removed by entering null
  }

  /** Iterates through the different snapshot of the heap, as well as the new added adresses.  */
  override def iterator: Iterator[(Vector[String], iTabSymb[Int])] = new Iterator[(Vector[String], iTabSymb[Int])] {
    //initialisation of iterator
    var liveVar = liveVars.head
    place(liveVar) //not sure we should do that, because parameters are already placed.
    var liveVarLeft = liveVars.tail
    var packetLeft = packets

    override def hasNext: Boolean = packetLeft.nonEmpty

    /**
     * computes *
     *
     * @return memory state string occupying each place, and adress associated to each string
     */
    override def next(): (Vector[String], iTabSymb[Int]) = {
      val p = packetLeft.head
      val newAllocatedAdress: List[String] = p.names
      place(new LinkedHashSet[String] ++ newAllocatedAdress)
      val res = heap //state will evolve with the following unplace, we need to point to the heap's state before that unplace.
      val l = liveVarLeft.head
      unPlace(p.names.toSet.union(liveVar).diff(l))
      liveVar = l
      packetLeft = packetLeft.tail
      liveVarLeft = liveVarLeft.tail
      (res, HashMap() ++ newAllocatedAdress.map((s: String) => (s, adress(s))))
    }
  }
}

