package dataStruc

import compiler.{ASTB, Instr}
import compiler.ASTB.{Both, InputStored, OutputStored}
import compiler.Circuit.{TabSymb, iTabSymb}

import scala.collection.{Iterable, Map, Set, immutable}
import scala.collection.immutable.{HashMap, HashSet}


/**
 * adds fonctionnality to Dag  whose nodes have mutable input,output neigbors,  defined by names
 *
 * @tparam T Dagnode's types
 */
trait DagWired[T <: WiredInOut[T]] extends Dag[T] {
  self: Dag[T] =>

  /**
   *
   * @param p predicat de deux objet T, vrai si ces deux objets sont dans la même composante connexes.
   * @tparam T2 Output dagNodes type
   * @param trans a partir d'une composante connexe, calcule un ou plusieurs neoud du output Dag cible
   * @return new dag produced by computing the connected components, and then transforming them
   */
  def quotient2[T2 <: DagNode[T2] with WiredInOut[T2]](p: (T, T) => Boolean, trans: Iterable[T] => List[T2]): Dag[T2] = {
    val newDagNodes = components2(p).flatMap(trans).toList //when applied to zone, an alignement is computed on  T's.
    WiredInOut.setInputAndOutputNeighbor(newDagNodes)
    val newGenerators = newDagNodes.filter({ case a: WiredInOut[_] => a.outputNeighbors.isEmpty; case _ => true }) // generators are dagNodes with no output
    new Dag(newGenerators) //reconstruct dag from generators,

  }

  /**
   *
   * @param outputStored property of nodes
   * @return for each string s, usedBy(s) is the nearest set of node used by s, verifying outputStored
   */
  def usedBy(outputStored: (T) => Boolean): HashMap[String, Set[String]] = {
    var res: immutable.HashMap[String, Set[String]] = HashMap() ++ visitedL.map(x => x.names(0) -> Set()) //set initially empty?
    for (node: T <- visitedL.reverse)
      if (outputStored(node)) res = res + (node.names(0) -> Set(node.names(0))) //we put the node itself if it is output Stored
      else for (inputNode: T <- node.inputNeighbors)
        if (outputStored(inputNode))
          res = res + (node.names(0) -> (res(node.names(0)) + (inputNode.names(0))))
        else
          res = res + (node.names(0) -> (res(node.names(0)) ++ res(inputNode.names(0))))
    res
  }

  /**
   *
   * @param outputStored property of nodes
   * @return for each string s, isUsing(s) is the nearest set of node using s, verifying outputStored
   */
  def isUsing(outputStored: (T) => Boolean): HashMap[String, Set[String]] = {
    var res: immutable.HashMap[String, Set[String]] = HashMap() ++ visitedL.map(x => x.names(0) -> Set()) //set initially empty?
    for (node: T <- visitedL)
      if (outputStored(node)) res = res + (node.names(0) -> Set(node.names(0)))
      else for (outputNode: T <- node.outputNeighbors)
        if (outputStored(outputNode))
          res = res + (node.names(0) -> (res(node.names(0)) + (outputNode.names(0))))
        else
          res = res + (node.names(0) -> (res(node.names(0)) ++ res(outputNode.names(0))))
    res
  }

  /**
   * @param isBool predicate on instruction T, returns true if instruction is boolean
   * @tparam T2
   * @return packets as connected components, sorted topologically.
   *         packets  are  either basic Boolean constructor OR, AND, XOR, NOT for boolean affectations
   *         or boolean (Reduce,Elt constructor) or Affect produced by spatical unfolding, or pipelined integer
   *         All the elements of one packet are to be executed in a single parallel loop
   */
  def packetize4ASTB[T2 <: DagNode[T2] with WiredInOut[T2]](isBool: (T) => Boolean): List[List[T]] = {
    val wrap: Map[T, Wrap] = immutable.HashMap.empty[T, Wrap] ++ visitedL.map(x => x -> Wrap(x))

    /** cheks that all integer have compatible scanning directions */
    def sameDirs(trial: T, s: List[T]): Boolean = {
      val d = ASTB.instrDirection(trial)
      for (out <- s) {
        val d2 = ASTB.instrDirection(out)
        if (d != d2
          && d != Some(Both()) && d2 != Some(Both()) //if one dir is Both, it could be either Left or Right so no pb
        ) return false
      }
      true
    }

    /**
     * needs to access the root, therefore needs access to the all attribute of components
     *
     * @param s outneighbor towards which "this" should fused
     * @return true if the element in the list can be fused . none of the boolean should be  used by an integer
     **/
    def canBeFused(s: List[T]): Boolean = {
      val roots = s.map(wrap(_).root).toSet //for each output neighbor, representant of its  packet
      val extendToEquivClass: Seq[T] = visitedL.filter((i: T) => roots.contains(wrap(i).root)) //elements which are in a packet of one output neighbor
      val potentialPbs = extendToEquivClass.filter(isBool(_)) //we consider only the booleans among those
      for (potentialPb: T <- potentialPbs) {
        val possibleTarget = s.filter(wrap(_).root != wrap(potentialPb).root).toSet //consider outneighbors which belongs to a class distinct from the considered boolean
        var exploreOut = HashSet(potentialPb)
        var fail = false //will now expore transitively the output of each boolean
        do {
          exploreOut = exploreOut.flatMap(_.outputNeighbors)
          fail = exploreOut.intersect(possibleTarget).nonEmpty //those cannot be produced in the same parallel loop
        }
        while (exploreOut.nonEmpty && (!fail))
        if (fail) return false
      };
      true
    }

    /** true if dagnodes can be unioned with all its output neighbors$ */
    val canBeUnionedToOutput = immutable.HashMap.empty[T, Boolean] ++ visitedL.map(
      (x: T) => x -> (isBool(x) && canBeFused(x.outputNeighbors) && sameDirs(x, x.outputNeighbors)))

    /** predicate defining connected component
     *
     * @param src    instruction creating a field $f
     * @param target instruction using that field
     * @return true if src and target should be in the same packet
     */
    def proximity(target: T, src: T): Boolean = canBeUnionedToOutput(src)

    val unsorted: Map[T, List[T]] = indexedComponents(proximity, wrap)

    topologicSort2(unsorted, wrap) //turned out we had to reprogram
  }


  /**
   * @param isBool predicate on instruction T, returns true if instruction is boolean
   * @tparam T2
   * @return packets as connected components, sorted topologically.
   *         packets  are  either basic Boolean constructor OR, AND, XOR, NOT for boolean affectations
   *         or boolean (Reduce,Elt constructor) or Affect produced by spatical unfolding, or pipelined integer
   *         All the elements of one packet are to be executed in a single parallel loop
   */
  def packetize4ASTB2[T2 <: DagNode[T2] with WiredInOut[T2]](isBool: (T) => Boolean): List[List[T]] = {
    val wrap: Map[T, Wrap] = immutable.HashMap.empty[T, Wrap] ++ visitedL.map(x => x -> Wrap(x))

    /** cheks that all integer have compatible scanning directions */
    def sameDirs(trial: T, s: List[T]): Boolean = {
      val d = ASTB.instrDirection(trial)
      for (out <- s) {
        val d2 = ASTB.instrDirection(out)
        if (d != d2
          && d != Some(Both()) && d2 != Some(Both()) //if one dir is Both, it could be either Left or Right so no pb
        ) return false
      }
      true
    }

    /** cheks that all integer have compatible scanning directions */
    def sameDir(t1: T, t2: T): Boolean = {
      val d1 = ASTB.instrDirection(t1)
      val d2 = ASTB.instrDirection(d1)
      if (d1 != d2 && d1 != Some(Both()) && d2 != Some(Both()) //if one dir is Both, it could be either Left or Right so no pb
      ) return false
      true
    }

    /**
     * needs to access the root, therefore needs access to the all attribute of components
     *
     * @param s outneighbor towards which "this" should fused
     * @return true if the element in the list can be fused . none of the boolean should be  used by an integer
     **/
    def canBeFused(s: List[T]): Boolean = {
      val roots = s.map(wrap(_).root).toSet //for each output neighbor, representant of its  packet
      val extendToEquivClass: Seq[T] = visitedL.filter((i: T) => roots.contains(wrap(i).root)) //elements which are in a packet of one output neighbor
      val potentialPbs = extendToEquivClass.filter(isBool(_)) //we consider only the booleans among those
      for (potentialPb: T <- potentialPbs) {
        val possibleTarget = s.filter(wrap(_).root != wrap(potentialPb).root).toSet //consider outneighbors which belongs to a class distinct from the considered boolean
        var exploreOut = HashSet(potentialPb)
        var fail = false //will now expore transitively the output of each boolean
        do {
          exploreOut = exploreOut.flatMap(_.outputNeighbors)
          fail = exploreOut.intersect(possibleTarget).nonEmpty //those cannot be produced in the same parallel loop
        }
        while (exploreOut.nonEmpty && (!fail))
        if (fail) return false
      };
      true
    }

    /** true if dagnodes can be unioned wiht all its output neighbors$ */
    val canBeUnionedToOutput = immutable.HashMap.empty[T, Boolean] ++ visitedL.map(
      (x: T) => x -> (isBool(x) && canBeFused(x.outputNeighbors) && sameDirs(x, x.outputNeighbors)))

    /** predicate defining connected component
     *
     * @param src    instruction creating a field $f
     * @param target instruction using that field
     * @return true if src and target should be in the same packet
     */
    def proximity(target: T, src: T): Boolean = canBeUnionedToOutput(src)

    val unsorted: Map[T, List[T]] = indexedComponents(proximity, wrap)

    topologicSort2(unsorted, wrap) //turned out we had to reprogram
  }


  /**
   *
   * @param unsorted list of packets of dag nodes not topologically sorted
   * @param wrap     allows to acess the roots
   * @return Sorted packets start from the leaf adding only leaf
   */
  def topologicSort2(unsorted: Map[T, List[T]], wrap: Map[T, Wrap]) = {
    var roots: Predef.Set[T] = visitedL.map(wrap(_).root.elt).toSet //set of roots
    var res = List[List[T]]() // the result
    var leaveLeft = unsorted

    /**
     * @return first leave in leaveleft encountered that verifies that non of its input neighbors has its root in roots
     */
    def nextFreeLeave2(): List[T] = {
      for (leave <- leaveLeft.values)
        if (isFree2(leave))
          return leave
      throw new Exception("on trouve pas de prochaine leave")
    }


    /** a leave isFree if all of its inputs's root have already been taken out of roots */
    def isFree2(leave: List[T]): Boolean = {
      for (elt <- leave) {
        val s = immutable.HashSet[T]() ++ leave.flatMap(_.inputNeighbors).map(wrap(_).root.elt) - wrap(leave.head).root.elt
        if (s.intersect(roots).nonEmpty) return false
      }
      true
    }

    while (roots.nonEmpty) {
      val l: List[T] = nextFreeLeave2() //next free packet
      roots = roots - wrap(l.head).root.elt //removes the corresponding root
      leaveLeft = leaveLeft - wrap(l.head).root.elt //and the corresponding leave
      res = l :: res //updates the result
    }
    res
  }


  def sortedIndexedComponents(p: (T, T) => Boolean,
                              all: Map[T, Wrap] = immutable.HashMap.empty[T, Wrap] ++ visitedL.map(x => x -> Wrap(x))) = {

    for (src <- visitedL) for (target <- src.inputNeighbors) if (p(src, target)) all(src).union(all(target)) //computes a common root for elements of one component
    topologicSort2(visitedL.groupBy(all(_).root.elt), all)
  }


  /**
   *
   * @param dagNodes List of Dag's elements
   * @return returns the max element of the list, by filtering  out  elements who  have output Neighbors in the list
   */
  def sup(dagNodes: List[T]) = {
    val s = dagNodes.toSet
    dagNodes.filter(_.outputNeighbors.toSet.intersect(s).isEmpty)
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
   * @param rewrite    rewrites each instruction into one instruction, preserve generators
   * @param otherInstr more instructions to be be added
   * @return New Dag with rewritten instructions, with  updated inputneighbors.
   */
  def propagateUnitKeepGenerators(rewrite: T => T, otherInstr: List[T] = List()): Dag[T] = {
    val newGenerators = (allGenerators).map(rewrite)
    val newNonGenerators = nonGenerators.map(rewrite)
    WiredInOut.setInputAndOutputNeighbor(newGenerators ::: newNonGenerators ::: otherInstr)
    new Dag(newGenerators) //reconstruit quand meme tout le Dag ca devrait assurer le bon ordre
  }

  /**
   * @param rewrite    each instruction into instruction,
   * @param otherInstr more instructions to be be added
   * @return Like propagate instead we work only on visitedL, because we want to keep the schedule.
   **/
  def propagateUnitKeepSchedule(rewrite: T => T, otherInstr: List[T] = List()) = {
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



  /**
   *
   * @param rewrite    each instruction is rewritten into O,1, or several instruction, preserve generators
   * @param otherInstr more instructions to be be added
   * @return New Dag with rewritten instructions, with  updated inputneighbors.
   *         in general  rewriting of generators may not produce  generators, for example, in the case of the zone dag
   **/
  def propagate(rewrite: T => List[T], otherInstr: List[T] = List()): Dag[T] = {
    val newGenerators = (allGenerators).flatMap(rewrite)
    val newNonGenerators = nonGenerators.flatMap(rewrite)
    WiredInOut.setInputAndOutputNeighbor(newGenerators ::: newNonGenerators ::: otherInstr)
    new Dag(newGenerators)
  }

  /**
   *
   * @param rewrite    each instruction is rewritten into O,1, or several instruction, preserve generators
   * @param otherInstr more instructions to be be added , we do not know where to insert them
   * @return New Dag with rewritten instructions, with  updated inputneighbors.
   *         in general  rewriting of generators may not produce  generators, for example, in the case of the zone dag
   **/
  def propagateUnit3(rewrite: T => T, otherInstr: List[T] = List()): Unit = {
    visitedL = visitedL.map(rewrite)
    WiredInOut.setInputAndOutputNeighbor(visitedL ::: otherInstr)
    insertAfterLastUsedAffect(otherInstr)
    //visitedL=(otherInstr.reverse):::visitedL  //this would insert  the looping on variables at the end, which is not suitable
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


  /**
   * @param p         proximity predicate
   * @param alignPerm alignement table for transfer variables v1 computed as exp where v2 apears in exp, a((v1,v2) indicates how to align v1 on v2
   * @return Iterable of instructions  with common root,  alignement on root for each instructions,
   */
  def alignedComponents(p: (T, T) => Boolean, alignPerm: Map[(String, String), Array[Int]]): (Iterable[List[T]], Map[String, Array[Int]], Map[String, T]) = {
    /** Uses the union find algorithm with wrap */
    case class Wrap(elt: T) extends Union[Wrap] with dataStruc.Align2[Wrap] {
      /**
       * @param n neighbor
       * @return alignement of this with respect to n
       */
      override def neighborAlign(n: Wrap): Array[Int] = {
        if (alignPerm.contains((elt.names.head, n.elt.names.head))) //n is a used var of this, so "this" is an element of n.neighbor,
        alignPerm((elt.names.head, n.elt.names.head)) //neighborAligned(n.names(0))  is an alignement from "this" to n,
        else if (alignPerm.contains((n.elt.names.head, elt.names.head))) //otherwise, it must be the opposite i.e. this is a used var of n. we find an alignement from n to "this", we invert
        Align2.invert(alignPerm((n.elt.names.head, elt.names.head)))
        else null //throw new RuntimeException(" Not find alignement ")
      }
    }
    //computes transfer variables which are names for which some alignemnent are defined, it is orirented, this is why shift do not appear..
    val transferVariable: Set[String] = HashSet() ++ alignPerm.map({ case ((name, _), _) => name })
    //println(transferVariable)
    /** mapping allowing  to find the wrapper of a given instruction */
    val wrap = immutable.HashMap.empty[T, Wrap] ++ visitedL.map(x => x -> Wrap(x))
    for (src <- visitedL) for (target <- src.inputNeighbors) if (p(src, target)) wrap(src).union(wrap(target)) //computes a common root for elements of one component
    val alignToRoot = immutable.HashMap.empty[String, Array[Int]] ++ visitedL.map(x => x.names.head -> wrap(x).alignToRoot)
    val myRoot = immutable.HashMap.empty[String, T] ++ visitedL.map(x => x.names.head -> wrap(x).root.elt)
    (visitedL.groupBy(wrap(_).root).values, alignToRoot, myRoot)
  }

  /* def quotientAlign[T2 <: DagNode[T2] with WiredInOut[T2]](p: (T, T) => Boolean,
             trans: Iterable[T] => List[T2], a: Map[(String,String),Array[Int]]): (Dag[T2],Map[String,Array[Int]]) = {
     val (groupNodes: Iterable[List[T]],align2root) = alignedComponents(p,a) //when applied to zone, an alignement is computed on  T's.
     println(printSched(align2root,groupNodes))
     val newDagNodes=groupNodes.flatMap(trans).toList
     WiredInOut.setInputAndOutputNeighbor(newDagNodes)
     val newGenerators = newDagNodes.filter({ case a: WiredInOut[_] => a.outputNeighbors.isEmpty; case _ => true }) // generators are dagNodes with no output

     (new Dag(newGenerators),align2root) //reconstruct dag from generators,

   }*/
}

object DagWired{



}


