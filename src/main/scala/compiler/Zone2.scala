package compiler

import compiler.Circuit.TabSymb
import compiler.Constraint.{Partition, empty, noneIsEmpty, propagate}
import compiler.Instr.a
import dataStruc.{DagNode, SetInput, toSet, SetOutput}
import scala.collection.Iterable
import scala.collection.immutable.{HashMap, HashSet}

/**
 *
 * @param root
 * @param schedule            constraint to be met for node to be foldable
 * @param partition           for each input zone, gives the associated partition.
 * @param nonPartitionnedEdge Edge without partition
 */
class Zone2(val root: Affect[_],

            /** Constraint for folding. it is progressively refined, until picking
             * whereby only one single schedule to be followed */
            var schedule: Constraint,

            /** stores partition constraints towards adjacent zones  */
            var partition: HashMap[String, Partition],

            /** list names of adjacent zones with no partition constraints   */
            var nonPartitionnedEdge: HashSet[String])
  extends DagNode[Zone2] with SetInput[Zone2] with SetOutput[Zone2] {
  /** Locus of root */
  def locus = root.locus.get

  /** name of variable set by root instruction */
  def name: String = a(root).name

  def names = List(name)

  def neighbors = inputNeighbors ++ outputNeighbors

  def usedVars: HashSet[String] = toSet(partition.keySet.toList).union(nonPartitionnedEdge)

  /** true is the several scalar registers encoding the locus can coalesc into a single register */
  var folded: Boolean = !schedule.empty; //if isV schedule must be empty
  /** true for transfer zone */
  def isTransfer = locus.isTransfer

  /** prints the name, the locus, whether it is folded, the current constraints, and the edges */
  override def toString: String = " Node " + name + " " + (if (!folded) "not" else "") + "folded" +
    " constr:  " + schedule + " IN-edges: [" + inputNeighbors.map(_.name) + "]" +
    " OUT-edges: [" + outputNeighbors.map(_.name) + "]" + "\n"

  /** Check output neighbor to compute partition attached to output edges. */
  def setPartitionOut(): Unit = for (n <- outputNeighbors) if (n.partition.contains(name)) partition += (n.name -> n.partition(name))

  private def partitionned(z: Zone2) = partition.contains(z.name)

  def addConstr(c: Constraint) = schedule = schedule.intersect(c)

  /**
   * for non-vertex SCC,
   * Intersect neighbor TCC's constraint with  partition constraint, input AND OUTPUT neighbors.
   * if all neighbors which where foldable still is, we try to fold
   * propagate the neighbor TCC's constraint through the partition, to the SCC
   */
  def setFoldConstrSimplicial(): Unit =
    if (locus == E() || locus == F()) {
      val partNeighbors = neighbors.filter(z => partitionned(z) && z.folded) //zone V are filtered out.
      /** new schedule for neighboring transfer zones, */
      val newSched = partNeighbors.map((z: Zone2) => z.schedule.intersect(partition(z.name)))
      if (!noneIsEmpty(newSched))
        folded = false
      else { // if one is empty, we renounce, transfer zone 's priority of folding
        // is higher than simplicial zone.
        var myNewSched = schedule
        for ((z, c) <- (partNeighbors zip newSched))
          myNewSched = myNewSched.intersect(propagate(partition(z.name), c))
        if (myNewSched.empty) folded = false else {
          folded = true;
          schedule = myNewSched;
          for ((z, c) <- (partNeighbors zip newSched)) z.schedule = c
        }
      }
    }

  /** For folded node,
   * all the input neighbors of "this" which are folded have already applied pick, and have a single schedule
   * we propagate those single schedule using the partition constraint, and intersect with the current constraint.
   * if the resulting constraint is not empty, we set folded to true
   * and also pick a single schedule in this resulting constraint.
   * otherwise we leave the constraint unchanged
   * */
  def pick() = if (folded) {
    val foldedInNeighbors = inputNeighbors.filter(_.folded) //we consider only folded neighbors.
    val propagateConstr = foldedInNeighbors.map((z: Zone2) => propagate(partition(z.name), z.schedule))
    val newConstr = Constraint.intersect(schedule :: propagateConstr, schedule.locus)
    if (newConstr.empty) folded = false
    else schedule = newConstr.pick()
  }
}

object Zone2 {
  /**
   * @param constraints constrains computed during the align phase
   * @param instrs      instructions associated to the zone.
   * @return a zone with partition computed towards input neighbors zone
   *
   */
  def apply(constraints: TabSymb[Constraint], instrs: Iterable[Affect[_]]) = {
    /**
     *
     * @param i  source instruction
     * @param i2 destination instruction
     * @return the partition constraint linking the two, if there is one.
     */
    def partition(i: Instr, i2: Instr): Option[Partition] = {
      require(i.isTransfer ^ i2.isTransfer)
      val iloc = i.locus.get;
      val i2loc = i2.locus.get
      if (iloc == V() || i2loc == V()) None else Some( //throw new RuntimeException("no partition towards V" + i + i2 )
        if (i.isTransfer) //$i2 is simplicial
        {
          val partition: Constraint = Partition(i.alignPerm(a(i2).name), i2.locus.get.asInstanceOf[S], i.locus.get.asInstanceOf[TT]) //constraint on i 's schedule
          partition.permute(i.alignToRoot, i.root.locus.get).asInstanceOf[Partition]
        } //expressed with respect to the root.
        else { // $i is simplicial, $i2 is transfer
          val slocus = iloc.asInstanceOf[S]
          val partition = Partition(slocus.proj, slocus, i2.locus.get.asInstanceOf[TT]) //when doing a reduction,
          // the mapping from Tlocus to Slocus is constant, and determined by the slocus
          partition.permute(i2.alignToRoot, i2.root.locus.get) //align on root
        })
    }

    /**
     * @param i instruction visited
     * @return constraint of i if exists, aligned to i's root
     */
    def alignedConstr(i: Affect[_]): Option[Constraint] = {
      val n = i.name
      if (constraints.contains(n)) {
        val c = Some(constraints(n).permute(i.alignToRoot, i.root.locus.get))
        c
      } else None
    }

    val root = a(instrs.head.root);
    val locus = root.locus.get
    val aC: List[Constraint] = instrs.flatMap(alignedConstr(_)).toList
    val foldConstr = if (root.locus.get.isTransfer) Constraint.intersect(aC, locus)
    else if (root.locus.get == V()) empty(V()) //Vertex Zone are not folded.
    else Constraint.AllConstr(locus) //ya pas de contraintes générées sur les zones simpliciales
    val instrIntputInstr: Iterable[(Instr, Instr)] = instrs.flatMap((i: Instr) =>
      i.inputNeighbors.filter((i2: Instr) => i2.root != root).map((i, _))) //we consider inputNeigbors in a distinct zone
    var partitions = HashMap.empty[String, Partition]
    var nonPart = HashSet.empty[String]
    for ((i, i2) <- instrIntputInstr) {
      val name = a(i2.root).name; val p = partition(i, i2)
      if (p == None) nonPart = nonPart + name
      else partitions = partitions + (name -> p.get)
    }
    new Zone2(root, foldConstr, partitions, nonPart)
  }


}
