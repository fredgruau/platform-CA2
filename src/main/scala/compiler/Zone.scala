package compiler

import compiler.Circuit.TabSymb
import compiler.Constraint.{Partition, empty, noneIsEmpty, propagate}
import compiler.Instr.a
import dataStruc.{DagNode, SetInput, toSet, SetOutput}
import scala.collection.Iterable
import scala.collection.immutable.{HashMap, HashSet}

/**
 *
 * @param root               instruction representing the zone
 * @param constraintSchedule constraint to be met for node to be foldable
 * @param partitionnedIn     for each input zone, gives the associated partition.
 * @param nonPartitionnedIn  Edge without partition
 */
class Zone(val root: Affect[_],
           val instrs: Iterable[Affect[_]],

           /** Constraint for folding. it is progressively refined, until after picking
            * whereby only one single schedule is left to be followed */
           var constraintSchedule: Constraint,

           /** stores partition constraints towards adjacent zones (input and output neighbors?) indexed by their name  */
           var partitionnedIn: HashMap[String, Partition],

           /** list names of input adjacent zones with no partition constraints   */
           var nonPartitionnedIn: HashSet[String])
  extends DagNode[Zone] with SetInput[Zone] with SetOutput[Zone] {

  def checkInvariant = {
    if (partitionnedIn.keys.size + nonPartitionnedIn.size != inputNeighbors.size)
      throw new Exception("edge are either partitionned or not partitionned" +
        partitionnedIn.keys.size + "+" + nonPartitionnedIn.size + "!=" + neighbors.size)
  }

  /** Locus of root */
  def locus = root.locus.get

  /** name of variable affected by root instruction, it is used to name the zone */
  def name: String = root.name

  /**
   * @return used to build the neigbors using the SetInput[Zone] and SetOutput[Zone] trait
   */
  def names = List(name)

  /**
   * @return all the neighbors
   */
  def neighbors = inputNeighbors ++ outputNeighbors

  /**
   *
   * @return input zones's names
   */
  def usedVars(): HashSet[String] = toSet(partitionnedIn.keySet.toList).union(nonPartitionnedIn)

  /** true if the several scalar registers encoding the locus can be coalesced into a single machine register */
  var folded: Boolean = !constraintSchedule.empty;

  /** true for transfer zone */
  def isTransfer = locus.isTransfer

  /** prints the name, the locus, whether it is folded, the current constraints, and the edges */
  override def toString: String = {
    checkInvariant;
    " ***********Node " + name + (if (!folded) " not" else "") + " folded" +
      " constr:  " + constraintSchedule +
      " IN-edges: [" + inputNeighbors.map(_.name) + "]" +
      " OUT-edges: [" + outputNeighbors.map(_.name) + "]" + "\n" +
      instrs.toList.mkString("")
  }

  var partitionnedInOut: HashMap[String, Partition] = HashMap()

  /** adds partition constraints towards output neighbors */
  def addPartitionOut(): Unit =
    partitionnedInOut = partitionnedIn

  for (n <- outputNeighbors)
    if (n.partitionnedIn.contains(name)) partitionnedInOut += (n.name -> n.partitionnedIn(name))

  /**
   *
   * @param z adjacent zone
   * @return true if there is a partition constraint towards z
   */
  private def partitionned(z: Zone) = partitionnedInOut.contains(z.name)


  /**
   * if THIS is a non-vertex SCC,( simplicial zone)
   * Intersect input AND OUTPUT neighbor TCC's constraint with  partition constraint.
   * if neighbors which where foldable remains foldable,
   * we try to fold the SCC:
   * we propagate the neighbor TCC's constraint through the partition, to the SCC
   * and check that the resulting schedule is non-empty
   * TODO we should also try to fold SCC even if some TCC are not folded, and then propagate the resulting constraint to the Tcc.
   *
   */
  def setFoldConstrSimplicial(): Unit =
    if (locus == E() || locus == F()) {
      val partNeighbors = neighbors.filter(z => partitionned(z) && z.folded) //zone V are filtered out.
      /** new schedule for neighboring transfer zones, */
      val newSched = partNeighbors.map((z: Zone) => z.constraintSchedule.intersect(partitionnedInOut(z.name)))
      if (!noneIsEmpty(newSched))
        folded = false
      else { // if one is empty, we renounce, transfer zone 's priority of folding
        // is higher than simplicial zone.
        var myNewSched = constraintSchedule
        for ((z, c) <- (partNeighbors zip newSched))
          myNewSched = myNewSched.intersect(propagate(partitionnedInOut(z.name), c))
        if (myNewSched.empty) folded = false else {
          folded = true;
          constraintSchedule = myNewSched;
          for ((z, c) <- (partNeighbors zip newSched)) z.constraintSchedule = c
        }
      }
    }

  /** For folded node,
   * all the input neighbors of "this" which are folded have already applied pick, and have a single schedule
   * we propagate those single schedule using the partition constraint, and intersect with the current constraint.
   * if the resulting constraint is not empty, we set folded to true
   * and also pick a single schedule in this resulting constraint.
   * otherwise we leave the constraint unchanged and set folded to false
   * */
  def pick() = if (folded) {
    val foldedInNeighbors = inputNeighbors.filter(_.folded) //we consider only folded neighbors.
    // TODO why not consider all neighors to determine a schedule for everybody even unfolded zones
    val propagateConstr = foldedInNeighbors.map((z: Zone) => propagate(partitionnedInOut(z.name), z.constraintSchedule))
    val newConstr = Constraint.intersect(constraintSchedule :: propagateConstr, constraintSchedule.locus)
    if (newConstr.empty) folded = false
    else constraintSchedule = newConstr.pick()
  }

  def pickedSchedule = constraintSchedule.schedules.head
}

object Zone {
  /**
   * @param constraints cycle constrains computed during the align phase
   * @param instrs      instructions associated to the zone.
   * @return a zone with partition computed towards input neighbors zone
   *
   */
  def apply(constraints: TabSymb[Constraint], instrs: Iterable[Affect[_]]) = {
    /**
     *
     * @param i      source instruction
     * @param iInput instruction input to i, lying in a distinct zone
     * @return the partitionIn constraint linking the two, if there is one.
     */
    def partitionIn(i: Instr, iInput: Instr): Option[Partition] = {
      require(i.isTransfer ^ iInput.isTransfer) //one instruction is simplicial, and the other is transfer.
      val iloc = i.locus.get
      val i2loc = iInput.locus.get
      if (iloc == V() || i2loc == V()) None //"no partitionIn towards V"
      else Some(
        if (i.isTransfer) //$i2 is simplicial
        {
          val partition: Constraint = Partition(i.alignPerm(a(iInput).name),
            iInput.locus.get.asInstanceOf[S], i.locus.get.asInstanceOf[TT]) //constraint on i 's schedule
          partition.permute(i.alignToRoot, i.root.locus.get).asInstanceOf[Partition]
        } //expressed with respect to the root.
        else { // $i is simplicial, $i2 is transfer
          val slocus = iloc.asInstanceOf[S]
          val partition = Partition(slocus.proj, slocus, iInput.locus.get.asInstanceOf[TT]) //when doing a reduction,
          // the mapping from Tlocus to Slocus is constant, and determined by the slocus
          partition.permute(iInput.alignToRoot, iInput.root.locus.get) //align on root
        })
    }

    /**
     * @param i instruction visited
     * @return constraint of i if exists, aligned to i's root
     */
    def alignedConstr(i: Instr): Option[Constraint] = {
      val ns = i.names
      if (ns.size != 1) return None
      val n = ns.head
      if (constraints.contains(n)) {
        val c = Some(constraints(n).permute(i.alignToRoot, i.root.locus.get))
        c
      } else None
    }

    val root: Affect[_] = a(instrs.head.root);
    val locus = root.locus.get
    val aC: List[Constraint] = instrs.flatMap(alignedConstr(_)).toList
    val foldConstr = if (locus.isTransfer) Constraint.intersect(aC, locus)
    else if (locus == V()) empty(V()) //Vertex Zone are not folded.
    else Constraint.AllConstr(locus) //ya pas de contraintes générées sur les zones simpliciales
    /** couple of instruction where the second on is an input of the first one, in a distinct zone     */
    val instrIntputInstr: Iterable[(Instr, Instr)] = instrs.flatMap((i: Instr) =>
      i.inputNeighbors.filter((i2: Instr) => i2.root != root).map((i, _))) //we consider inputNeigbors in a distinct zone
    var partitionnedIn = HashMap.empty[String, Partition]
    var nonPartitionnedIn = HashSet.empty[String]
    for ((i, i2) <- instrIntputInstr) {
      val name = a(i2.root).name; val p = partitionIn(i, i2)
      if (p == None) nonPartitionnedIn = nonPartitionnedIn + name
      else partitionnedIn = partitionnedIn + (name -> p.get)
    }
    new Zone(root, instrs, foldConstr, partitionnedIn, nonPartitionnedIn)
  }


}
