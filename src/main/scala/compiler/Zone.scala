package compiler

import Circuit.TabSymb
import Constraint.{Partition, empty, noneIsEmpty, propagate}
import Instr.a
import dataStruc.{DagNode, Schedule, WiredInOut, isIdentity, toSet}
import scala.collection.{Iterable, Map}
import scala.collection.immutable.{HashMap, HashSet}

/**
 *
 * @param root               instruction representing the zone
 * @param constraintSchedule constraint to be met for node to be foldable.it is progressively refined, until  picking one single schedule
 * @param partitionnedIn     stores partition constraints towards adjacent zones (input and output neighbors?) indexed by their name
 * @param vars               name of variable computed by instructions exept those of transfer zone, except those whose alingment is not id.
 * @param nonPartitionnedIn  list names of input adjacent zones with no partition constraints
 * @param nonIdAlignToRoot   alignement of  variable computed by transfer instructions, when it is not not identity.
 */
class Zone(val root: Affect[_], val instrs: Iterable[Affect[_]], var constraintSchedule: Constraint,
           var partitionnedIn: HashMap[String, Partition], var nonPartitionnedIn: HashSet[String],
           private val vars: Set[String], private val nonIdAlignToRoot: Map[String, Array[Int]])
  extends DagNode[Zone] with WiredInOut[Zone] {

  def checkInvariant = {
    if (partitionnedIn.keys.size + nonPartitionnedIn.size != inputNeighbors.size)
      throw new Exception("edge are either partitionned or not partitionned" +
        partitionnedIn.keys.size + "+" + nonPartitionnedIn.size + "!=" + neighbors.size)
  }

  /** prints  the locus, the variable synchronized (aligned with id) the variable aligned with a spécific permutation,
   * whether it is folded, the current constraints, and the input and output edges to resp. variables used from computation done
   * in input zone, , variable in output zone, whose computation is using  computation done in this zone; */
  override def toString: String = {
    val toStringLocus = if (isTransfer) "TT" else "" + locus

    def toStringAlign = if (nonIdAlignToRoot.isEmpty) "" else (nonIdAlignToRoot.keys groupBy (nonIdAlignToRoot(_))).map({ case (k, v) => k.toSeq -> v }).mkString(",")

    def toStringFolded = if (locus == V()) "" else ((if (!folded) " not" else "") + " folded")

    def toStringConstr = if (locus == V()) "" else " constr:  " + constraintSchedule

    checkInvariant;
    "*****Zone " + toStringLocus +   " name : " +  name + " {" + vars.mkString(",") + "}" + toStringAlign + toStringFolded + toStringConstr +
      " IN-edges: [" + inputNeighbors.map(_.name) + "]" +
      " OUT-edges: [" + outputNeighbors.map(_.name) + "]" + "\n"+
      instrs.toList.mkString("")+ "\n"
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

  val id6: Array[Int] = Array(0, 1, 2, 3, 4, 5)

  /**
   * @param constraints cycle constrains computed during the align phase
   * @param instrs      instructions associated to the zone.
   * @param myRoot      mapping a name to the root instruction
   * @param align2root  alignement on root
   * @return a zone with partition computed towards input neighbors zone
   *
   */
  def apply(constraints: TabSymb[Constraint], instrs: Iterable[Affect[_]], alignPerm: Map[(String, String),
    Array[Int]], align2root: dataStruc.Schedule, myRoot: Map[String, Affect[_]]) = {
    /**
     *
     * @param i      source instruction
     * @param iInput instruction input to i, lying in a distinct zone
     * @return the partitionIn constraint linking the two, if there is one.
     */
    def partitionIn(i: Instr, iInput: Instr): Option[Partition] = {
      //require(i.isTransfer ^ iInput.isTransfer) //one instruction is simplicial, and the other is transfer. we now can have two SImplicial zone, neighbor, in order to break cycles.
      val iloc = i.locus.get
      val i2loc = iInput.locus.get
      if (iloc == V() || i2loc == V()) None //"no partitionIn towards V"
      else Some(
        if (i.isTransfer) //$i2 is simplicial
        {
          val partition: Constraint = Partition(alignPerm((i.names.head, a(iInput).name)),
            iInput.locus.get.asInstanceOf[S], i.locus.get.asInstanceOf[TT]) //constraint on i 's schedule
          partition.permute(align2root(a(i).name), (myRoot(i.names.head)).locus.get).asInstanceOf[Partition]
        } //expressed with respect to the root.
        else { // if $i is simplicial, $i2 is transfer
          val slocus = iloc.asInstanceOf[S]
          val partition = Partition(slocus.proj, slocus, iInput.locus.get.asInstanceOf[TT]) //when doing a reduction,
          // the mapping from Tlocus to Slocus is constant, and determined by the slocus
          partition.permute(align2root(a(iInput).name), myRoot(iInput.names.head).locus.get) //align on root
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
        val c = Some(constraints(n).permute(align2root(i.names.head), myRoot(i.names.head).locus.get))
        c
      } else None
    }

    val root: Affect[_] = myRoot(instrs.head.name);
    val locus = root.locus.get
    /** permutation constraints générée par les shift */
    val aC: List[Constraint] = instrs.flatMap(alignedConstr(_)).toList
    /** if satisfied, then zone can be folded */
    val foldConstr =
      if (locus.isTransfer) Constraint.intersect(aC, locus)
      else if (locus == V()) empty(V()) //Vertex Zone are not folded.
      else Constraint.AllConstr(locus) //pour le moment, ya pas de contraintes générées sur les zones simpliciales
    /** couple of instruction where the second on is an input of the first one, in a distinct zone     */
    val instrIntputInstr: Iterable[(Instr, Instr)] = instrs.flatMap((i: Instr) =>
      i.inputNeighbors.filter((i2: Instr) => myRoot(i2.names.head) != root).map((i, _))) //we consider inputNeigbors in a distinct zone
    var partitionnedIn = HashMap.empty[String, Partition]
    var nonPartitionnedIn = HashSet.empty[String]
    for ((i, i2) <- instrIntputInstr) {
      val name = a(myRoot(i2.names.head)).name
      val p = partitionIn(i, i2)
      if (p == None) nonPartitionnedIn = nonPartitionnedIn + name
      else partitionnedIn = partitionnedIn + (name -> p.get)
    }
    //compute synchronized variables
    var nonIdAlignToRoot: HashMap[String, Array[Int]] = HashMap()
    var vars: Set[String] = Set() ++ instrs.map(_.names.head)
    if (locus.isTransfer) {
      val (aligned, notAligned) = vars.partition((t: String) => isIdentity(align2root(t)))
      vars = aligned
      notAligned.map((t: String) => t + " " + align2root(t).mkString(":"))
      nonIdAlignToRoot = HashMap() ++ notAligned.map((t: String) => t -> align2root(t))
    }

    new Zone(root, instrs, foldConstr, partitionnedIn, nonPartitionnedIn, vars, nonIdAlignToRoot)
  }

}
