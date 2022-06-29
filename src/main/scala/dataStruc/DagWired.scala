package dataStruc

import compiler.ASTB
import compiler.ASTB.Both

import scala.collection.{Iterable, immutable}
import scala.collection.immutable.{HashMap, HashSet}


/**
 * DagUnion  whose nodes have mutable input,output neigbors,  defined by names
 *
 * @tparam T Dagnode's type
 */
trait DagWired[T <: Union[T] with WiredInOut[T]] extends DagUnion[T] //with DagSetInput2[T]
{
  self: Dag[T] =>
  /**
   *
   * @param p predicat de deux objet T, vrai si ces deux objets sont dans la même composante connexes.
   * @tparam T2 Output dagNodes type
   * @param trans a partir d'une composante connexe, calcule un ou plusieurs neoud du output Dag cible
   * @return
   */
  def quotientOld[T2 <: DagNode[T2] with WiredInOut[T2]](p: (T, T) => Boolean, trans: Iterable[T] => List[T2]): Dag[T2] = {
    val connectedComp: Iterable[Iterable[T]] = components(p)
    /** generators are instructions group which contains generators. */
    val (groupWithGenerator, groupWithoutGenerator) = connectedComp.partition(a => overlap(a, toSet(allGenerators)))
    var newGenerators: List[T2] = groupWithGenerator.flatMap(trans).toList
    val newNonGenerators: List[T2] = groupWithoutGenerator.flatMap(trans).toList
    WiredInOut.setInputAndOutputNeighbor(newGenerators ::: newNonGenerators)
    //generators have no output
    newGenerators = newGenerators.filter({ case a: WiredInOut[_] => a.outputNeighbors.isEmpty; case _ => true })
    new Dag(newGenerators)
  }

  /**
   *
   * @param p predicat de deux objet T, vrai si ces deux objets sont dans la même composante connexes.
   * @tparam T2 Output dagNodes type
   * @param trans a partir d'une composante connexe, calcule un ou plusieurs neoud du output Dag cible
   * @return
   */
  def quotient[T2 <: DagNode[T2] with WiredInOut[T2]](p: (T, T) => Boolean, trans: Iterable[T] => List[T2]): Dag[T2] = {
    val newDagNodes = components(p).flatMap(trans).toList //when applied to zone, an alignement is computed on  T's.
    WiredInOut.setInputAndOutputNeighbor(newDagNodes)
    val newGenerators = newDagNodes.filter({ case a: WiredInOut[_] => a.outputNeighbors.isEmpty; case _ => true }) // generators are dagNodes with no output
    new Dag(newGenerators) //reconstruct dag from generators,

  }

  /**
   *
   * @param p predicat de deux objet T, vrai si ces deux objets sont dans la même composante connexes.
   * @tparam T2 Output dagNodes type
   * @param trans a partir d'une composante connexe, calcule un ou plusieurs neoud du output Dag cible
   * @return
   */
  def quotient2[T2 <: DagNode[T2] with WiredInOut[T2]](p: (T, T) => Boolean, trans: Iterable[T] => List[T2]): Dag[T2] = {
    val newDagNodes = components2(p).flatMap(trans).toList //when applied to zone, an alignement is computed on  T's.
    WiredInOut.setInputAndOutputNeighbor(newDagNodes)
    val newGenerators = newDagNodes.filter({ case a: WiredInOut[_] => a.outputNeighbors.isEmpty; case _ => true }) // generators are dagNodes with no output
    new Dag(newGenerators) //reconstruct dag from generators,

  }

  /**
   * packets  are  either basic Boolean constructor OR, AND, XOR, NOT for boolean affectations
   * * or boolean (Reduce,Elt constructor) or Affect produced by spatical unfolding, or pipelined integer
   * * All the elements of one packet are to be executed in a single parallel loop
   *
   * @param isBool
   * @tparam T2
   * @return
   */
  def packetize4ASTB[T2 <: DagNode[T2] with WiredInOut[T2]](isBool: (T) => Boolean) = {

    /** cheks that all integer have identical directions */
    def sameDirs(trial: T, s: List[T]): Boolean = {
      val d = ASTB.dir2(trial)
      for (out <- s) {
        val d2 = ASTB.dir2(out)
        if (d != d2
          && d != Some(Both()) && d2 != Some(Both()) //if one dir is Both, it could be either Left or Right so no pb
        ) return false
      }
      true
    }

    /**
     *
     * @param s outneighbor towards which "this" should fused
     * @return fused is OK if none of the boolean is used by an integer
     **/
    def canBeFused(s: List[T]): Boolean = {
      val roots = s.map(_.root).toSet
      val extendToEquivClass = visitedL.filter((i: T) => roots.contains(i.root)) //builds the current equivalence class of this
      val potentialPbs = extendToEquivClass.filter(isBool(_)) //we gets the booleans of the considered equivalence class
      for (potentialPb <- potentialPbs) {
        val possibleTarget = s.filter(_.root != potentialPb.root).toSet //consider outneighbors which belongs to a class distinct from this
        var exploreOut = HashSet(potentialPb)
        var fail = false //will now expore transitively the output of each boolean
        do {
          exploreOut = exploreOut.flatMap(_.outputNeighbors)
          fail = exploreOut.intersect(possibleTarget).nonEmpty
        } //those cannot be produced in the same parallel loop
        while (exploreOut.nonEmpty && (!fail))
        if (fail) return false
      };
      true

    }

    for (src <- visitedL)
      if (!isBool(src)) { //boolean do not merge towards output
        val b1 = canBeFused(src.outputNeighbors)
        val b2 = sameDirs(src, src.outputNeighbors)
        if (b1 && b2)
          for (out <- src.outputNeighbors)
            src.union(out)
      }

    val unsorted: Predef.Map[T, List[T]] = Union.indexedPaquets(visitedL)
    topologicSort(unsorted) //turned out we had to reprogramm
  }

  /** a leave isFree if all of its inputs's root have already been taken out of roots */
  def isFree(leave: List[T], roots: Predef.Set[T]): Boolean = {
    for (elt <- leave) {
      val s = immutable.HashSet[T]() ++ leave.flatMap(_.inputNeighbors).map(_.root) - leave.head.root
      if (s.intersect(roots).nonEmpty) return false
    }
    true
  }

  /** returns first leave encountered that verifies that non of its input neighbors has its root in roots */
  def nextFreeLeave(leaveLeft: Predef.Map[T, List[T]], roots: Predef.Set[T]): List[T] = {
    for (leave <- leaveLeft.values)
      if (isFree(leave, roots))
        return leave
    throw new Exception("on trouve pas de prochaine leave")
  }

  /** Sort equivalence class starting from the leaf adding only leaf  */
  def topologicSort(unsorted: Predef.Map[T, List[T]]) = {
    var roots = visitedL.map(_.root).toSet //as usual, root represent equivalence class
    var res = List[List[T]]()
    var leaveLeft = unsorted
    while (roots.nonEmpty) {
      val l = nextFreeLeave(leaveLeft, roots)
      roots = roots - l.head.root
      leaveLeft = leaveLeft - l.head.root
      res = l :: res
    }
    res
  }

  /** elements who do not have output Neighbors in the components are the one
   * not in pipelined, that will need an affect. */
  def sup(comp: List[T]) = {
    val s = comp.toSet
    comp.filter(_.outputNeighbors.toSet.intersect(s).isEmpty)
  }

  /**
   * insert instructions at the right place
   * we scan visitedL starting from the last instructions and insert the new affect when nobody uses them
   * * @param otherInstr instruction factorizing code
   */
  private def insertBeforeFirstUse(otherInstr: List[T]) = {
    var res: List[T] = List.empty
    var nbUser: HashMap[T, Int] = HashMap.empty ++ otherInstr.map((instr: T) => (instr -> instr.outputNeighbors.size)) //compte les output
    for (instr <- visitedL) {
      res ::= instr
      for (other <- instr.inputNeighbors) {
        if (nbUser.contains(other)) {
          nbUser += (other -> (nbUser(other) - 1))
          if (nbUser(other) == 0)
            res ::= other
        }
      }
    }
    visitedL = res.reverse
  }

  /**
   *
   * @param rewrite    each instruction is rewritten into O,1, or several instruction, preserve generators
   * @param otherInstr more instructions to be be added
   * @return Like propagate instead we work only on visitedL, because we want to keep the schedule.
   **/
  def propagateUnit2(rewrite: T => T, otherInstr: List[T] = List()) = {
    visitedL = visitedL.map(rewrite)
    WiredInOut.setInputAndOutputNeighbor(visitedL ::: otherInstr)
    insertBeforeFirstUse(otherInstr)
  }

  /**
   * we insert newId <-exp after the affectations that uses newId
   * and after the affectation that defines variable used by newId
   * After folding, the register used in exp may have change their value and
   * todo we should chek that it is not the case.
   *
   * @param otherInstr
   */
  private def insertAfterLastUsedAffect(otherInstr: List[T]) = {
    var res: List[T] = List.empty
    var nbUsed: HashMap[T, Int] = HashMap.empty ++ otherInstr.map((instr: T) => (instr -> (1 + instr.inputNeighbors.size))) //compte les output
    val myBossToMe: HashMap[T, T] = HashMap.empty ++ otherInstr.map((instr: T) => (instr.outputNeighbors.head -> instr))

    for (instr <- visitedL.reverse) {
      res ::= instr
      if (myBossToMe.contains(instr)) { //we found the boss, the affectation using the tm1
        val other = myBossToMe(instr)
        nbUsed += (other -> (nbUsed(other) - 1))
        if (nbUsed(other) == 0) //yes we can insert
        res ::= other
      }
      for (other <- instr.outputNeighbors) {
        if (nbUsed.contains(other)) {
          nbUsed += (other -> (nbUsed(other) - 1))
          if (nbUsed(other) == 0) //yes we can insert
          res ::= other
        }
      }
    }

    visitedL = res
  }

  def propagateUnit3(rewrite: T => T, otherInstr: List[T] = List()) = {
    visitedL = visitedL.map(rewrite)
    WiredInOut.setInputAndOutputNeighbor(visitedL ::: otherInstr)
    insertAfterLastUsedAffect(otherInstr)
    //visitedL=(otherInstr.reverse):::visitedL  //this would insert  the looping on variables at the end, which is not suitable
  }


  /**
   *
   * @param rewrite    rewrites each instruction into one instruction, preserve generators
   * @param otherInstr more instructions to be be added
   * @return New Dag with rewritten instructions, with  updated inputneighbors.
   */
  def propagateUnit(rewrite: T => T, otherInstr: List[T] = List()): Dag[T] = {
    val newGenerators = (allGenerators).map(rewrite)
    val newNonGenerators = nonGenerators.map(rewrite)
    WiredInOut.setInputAndOutputNeighbor(newGenerators ::: newNonGenerators ::: otherInstr)
    new Dag(newGenerators) //reconstruit quand meme tout le Dag ca devrait assurer le bon ordre

  }

  /**
   *
   * @param rewrite    each instruction is rewritten into O,1, or several instruction, preserve generators
   * @param otherInstr more instructions to be be added
   * @return New Dag with rewritten instructions, with  updated inputneighbors.
   *         we are not sure wether rewriting of generators produces only generators
   *         TODO in fact it is not true when creating zone DAG
   **/
  def propagate(rewrite: T => List[T], otherInstr: List[T] = List()): Dag[T] = {
    val newGenerators = (allGenerators).flatMap(rewrite)
    val newNonGenerators = nonGenerators.flatMap(rewrite)
    WiredInOut.setInputAndOutputNeighbor(newGenerators ::: newNonGenerators ::: otherInstr)
    new Dag(newGenerators)
  }


  /**
   *
   * @param rewrite    each instruction is rewritten into O,1, or several instruction
   * @param otherInstr more instructions to be be added
   * @return New Dag with rewritten instructions.
   *         dag's instructions are visited in reverse order
   *         since they are stored in reversed order
   *         they end up being visited in the natural order
   */
  def propagateReverse(rewrite: T => T, otherInstr: List[T] = List()): Dag[T] = {
    val newNonGenerators = nonGenerators.reverse.map(rewrite).reverse
    val newGenerators = (allGenerators).reverse.map(rewrite).reverse
    WiredInOut.setInputAndOutputNeighbor(newGenerators ::: newNonGenerators ::: otherInstr)
    new Dag(newGenerators)
  }

}


