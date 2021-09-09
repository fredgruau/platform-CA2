package dataStruc

import compiler.{AST, Instr}
import dataStruc.DagInstr.setInputAndOutputNeighbor
import dataStruc.DagNode.paquets
import scala.collection.{mutable, _}
import scala.collection.immutable.HashSet
/**
 * Node of a Directed Acyclic Graph (DAG)
 * getCycle is used to test the absence of cycles
 * getGreater is used to collect all the nodes of a Dag,
 * whose set of minimum is passed or completed on the fly
 * neighbor is   an edge used with depth first search,
 * other is not an edge. It points to other nodes to explore the whole DAG
 * to complete on the fly an initial set of minimals
 */
trait DagNode[T <: DagNode[T]] {
  def inputNeighbors: List[T]

  /** others are node that should be visited, but are not input neighbors. by default there is none */
  def other: List[T] = List.empty

  def toStringTree: String = toString + " " +
    (if (inputNeighbors.size > 1 || this.isInstanceOf[AST.Neton[_]]) "(" + inputNeighbors.map(_.toStringTree).foldLeft("")(_ + ", " + _).substring(2) + ")" //le substring vire la premiere virgule
    else if (inputNeighbors.size == 1) inputNeighbors.head.toStringTree else " ")
}


object Dag {
  def apply[T <: DagNode[T]]() = new Dag(List[T]())

  def apply[T <: DagNode[T]](g: List[T]) = new Dag(g)

  /**
   * Tries to find a cycle
   *
   * @param n starting node to reach the cycle
   * @return the cycle if a cycle is found, else none
   */

  def getCycle2[T <: DagNode[T]](n: T): Option[Vector[T]] = {
    val d = new Dag[T]; d.dfs(n, Vector.empty)
  }
}

/**
 * Represents an entire Directed acylic Graph
 *
 * @param generators optional initial generators
 * @tparam T
 */
class Dag[T <: DagNode[T]](generators: List[T]) {
  //TODO put all the fields in the constructor to avoid recomputing when transtlatin dag[Instr] into DagInstr
  def this() = this(List())

  /** We create an exeption which can store the cycle
   * in order to be able to print it nicely later
   * nicely means with names  identifying fiedls in the client program */
  class CycleException(val cycle: Vector[T]) extends Exception("cycle détecté") {}

  //def setInputNeighbor(instrs: List[T] ) = ()

  /**   all the generators -maximal elements- from which all the other can be reached */
  var allGenerators: List[T] = List() //TODO maintain nonGenerator together with allGenerator, and forget visitedL
  /** @return non maximal dag's element */
  def nonGenerators(): List[T] = {
    val aG = HashSet.empty[AST[_]] ++ allGenerators
    visitedL.filter(!aG.contains(_))
  }

  /** all visited dag's node, ordered with generators first. */
  var visitedL: List[T] = List()
  /** newly visited node */
  private var newVisitedL: List[T] = List()
  var visited: HashSet[T] = HashSet()
  addGenerators(generators) //visits all the Dag's nodes
  override def toString = allGenerators.map(_.toStringTree).mkString("\n")


  /**
   * add new generators to the Dag together with nodes which can be accessed from those.
   *
   * @param newGenerators generators possibly not in the DAG yet.
   * @return list of new node accessible from those newGenerators.
   */
  def addGenerators(newGenerators: List[T]): List[T] = {
    allGenerators ++= newGenerators
    //so that we can get which are the new nodes.
    newVisitedL = List()
    for (b <- newGenerators)
      dfs(b, Vector.empty) match {
        case Some(path) => throw new CycleException(path)
        //  case Some(path) => throw new RuntimeException("cycle detected in AST:" + path)
        case None =>
      }
    visitedL = newVisitedL ::: visitedL
    newVisitedL //returns newly visited nodes.
  }

  /**
   * update visited which contains all the node that can be reached from b using a depth first search (dfs)
   * if a cycle is generated, returns the corresponding path.
   * When we use case hierarchy, keys associated to distinct node, can be identical, and this subtelty
   * means that not all the nodes are visited, there is a single representant for each equivalence class.
   *
   * @param n        node to test
   * @param visiting nodes being checked for adding to visited.
   * @return option type with a cycle is there is one.
   */
  def dfs(n: T, visiting: Vector[T]): Option[Vector[T]] = {
    if (visited(n)) return None
    else if (visiting.contains(n))
      return Some(visiting.drop(visiting.indexOf(n) - 1))
    else {
      val visiting2 = visiting :+ n
      for (e <- n.inputNeighbors)
        dfs(e, visiting2) match {
          case Some(c) => return Some(c)
          case _ =>
        }
      visited = visited + n;
      newVisitedL = n :: newVisitedL
    }
    None
  }

  /** @param called input from outside usage which must also be counted
   * @return set of Dag's elements which are at least two times input to another dag's element */
  def inputTwice(called: Seq[T] = Seq.empty[T]): Set[T] = {
    /** Expression is used in a CallProc */
    val nUser2 = immutable.HashMap.empty[T, Int] ++
      (visitedL.flatMap(_.inputNeighbors) ++ called).groupBy(identity).map { case (k, v) ⇒ k -> v.size }
    toSet(visitedL.filter(e => nUser2.contains(e) && nUser2(e) > 1))
  }
}

/** Allows to compute input neighbors */
trait SetInput[T <: SetInput[T]] {
  /** to be set if we want to use the Dag feature. */
  var inputNeighbors: List[T] = List.empty;

  /** names of variables modified by instruction. */
  def usedVars: immutable.HashSet[String]
  def names: List[String]
}

/** Allows to compute output neighbors */
trait SetOutput[T <: SetOutput[T]] extends SetInput[T] {
  /** to be set if we want to use the Dag feature. */
  var outputNeighbors: List[T] = List.empty;
}

trait DagSetInput[T <: DagNode[T] with Union[T] with SetOutput[T]] extends Dag[T] {
  self: Dag[T] =>
  /**
   *
   * @param p     defines proximity so as to computes connected components of instructions
   * @param trans will compute one or several instructions associated to each group.
   * @return the quotient  DAG
   */
  def quotient2[T2 <: DagNode[T2] with SetOutput[T2]](p: (T, T) => Boolean, trans: Iterable[T] => List[T2]): Dag[T2] = {
    for (src <- visitedL)
      for (target <- src.inputNeighbors)
        if (p(src, target))
          src.union(target)
    val connectedComp: Iterable[Iterable[T]] = paquets(visitedL)
    /** generators are instructions group which contains generators. */
    val (groupWithGenerator, groupWithoutGenerator) = connectedComp.partition(a => overlap(a, toSet(allGenerators)))
    var newGenerators: List[T2] = groupWithGenerator.flatMap(trans).toList
    val newNonGenerators: List[T2] = groupWithoutGenerator.flatMap(trans).toList
    setInputAndOutputNeighbor(newGenerators ::: newNonGenerators)
    //generators have no output
    newGenerators = newGenerators.filter({ case a: SetOutput[_] => a.outputNeighbors.isEmpty; case _ => true })
    new Dag(newGenerators)
  }

  /**
   *
   * @param rewrite    each instruction into one instruction, preserve generators
   * @param otherInstr more instructions to be be added
   * @return New Dag with rewritten instructions, with  updated inputneighbors.
   */
  def propagateUnit(rewrite: T => T, otherInstr: List[T] = List()): Dag[T] = {
    val newGenerators = (allGenerators).map(rewrite)
    val newNonGenerators = nonGenerators.map(rewrite)
    setInputAndOutputNeighbor(newGenerators ::: newNonGenerators ::: otherInstr)
    new Dag(newGenerators) //reconstruit quand meme tout le Dag
  }

  /**
   *
   * @param rewrite    each instruction is rewritten into O,1, or several instruction, preserve generators
   * @param otherInstr more instructions to be be added
   * @return New Dag with rewritten instructions, with  updated inputneighbors.
   */
  def propagate(rewrite: T => List[T], otherInstr: List[T] = List()): Dag[T] = {
    val newGenerators = (allGenerators).flatMap(rewrite)
    val newNonGenerators = nonGenerators.flatMap(rewrite)
    setInputAndOutputNeighbor(newGenerators ::: newNonGenerators ::: otherInstr)
    new Dag(newGenerators)
  }

  /**
   *
   * @param rewrite    each instruction is rewritten into O,1, or several instruction
   * @param otherInstr more instructions to be be added
   * @return New Dag with rewritten instructions. order is reversed with respect to propagate
   */
  def propagateReverse(rewrite: T => T, otherInstr: List[T] = List()): Dag[T] = {
    val newNonGenerators = nonGenerators.reverse.map(rewrite).reverse
    val newGenerators = (allGenerators).reverse.map(rewrite).reverse
    setInputAndOutputNeighbor(newGenerators ::: newNonGenerators ::: otherInstr)
    new Dag(newGenerators)
  }

}

object DagNode {

  /**
   *
   * Depth First Search, Used to instanciate a hashset "visited" of the right type T <: Dag[T]
   *
   * @param visited hashset of visited nodes, allways augment
   * @tparam T Node of Dag
   */

  class DfsOld[T <: DagNode[T]](var visited: immutable.HashSet[T]) {
    def this() = this(immutable.HashSet.empty[T])

    /** VisitedL is a list version of visited,  used to preserve the order of visit */
    var visitedL: List[T] = List.empty
    def resetVisitedL()={visitedL=List.empty}

    /**
     * verify that there is no cycle within a graph, starting from a given node n
     * using a depth first search (dfs)
     * simultaneously update visited which contains all the node that can be reached from b
     * @param n  node to test
     * @return option type with a cycle is there is one.
     */
    def dfs(n: T, visiting: Vector[T]): Option[Vector[T]] = {
      if (visited(n)) return None
      else if (visiting.contains(n))
        return Some(visiting.drop(visiting.indexOf(n) - 1))
      else {
        val visiting2 = visiting :+ n
        for (e <- n.inputNeighbors)
          dfs(e, visiting2) match { case Some(c) => return Some(c) case _ => }
        visited = visited + n
        visitedL = n :: visitedL
        //visit "other" nodes met on the fly (in the next part of layers)
         for (e <- n.other) if (!visiting.contains(e) && e != n)
           dfs(e, Vector.empty) match { case Some(c) => return Some(c) case _ => }
      }
      None
    }
  }
  /**
   * Compute the set of nodes of a DAG
   * throw an exeption if the graph is not a DAG
   * T<:Dag[T] means that neighbor are also of the same type
   * @param minimals, set of DAG's minimal. easier to process as a list.
   * @param visited, already visited nodes.
   * @return nodes greater than those
   */
  def getGreater[T <: DagNode[T]](minimals: List[T], visited:  immutable.HashSet[T]): (List[T], HashSet[T]) =
    {
      val dfs = new DfsOld[T](visited)
      for (b <- minimals)
        dfs.dfs(b, Vector.empty) match {
          case Some(path) => throw new RuntimeException("cycle detected in AST:" + path)
          case None       =>
        }
      (dfs.visitedL, dfs.visited)
    }

  def getGreater[T <: DagNode[T]](minimals: List[T]): (List[T], immutable.HashSet[T]) = getGreater(minimals,  immutable.HashSet.empty[T])

  /**
   * computes the connected components the resulting partition is a kind of list of list, (iterable of Iterable)
   * The DAG must extends union so as to have the necessary private field myroot,rank,parent, plus the code of union.
   * @param p  predicate defines adjacence
   */
  def components[T <: DagNode[T] with Union[T]](all: List[T], p: (T, T) => Boolean): Iterable[Iterable[T]] = {
    for (src <- all) for (target <- src.inputNeighbors) if (p(src, target)) src.union(target)
    paquets(all) }

  /** regroup in distincts iterable,  elements of toSort having identical root */
  def paquets[T <: DagNode[T] with Union[T]](toSort: List[T]):immutable.Iterable[Iterable[T]] = {
    val m = mutable.LinkedHashMap.empty ++ toSort.map(x => x -> x.root)
    m.groupBy(_._2).map { case (_, v) => v.keys }
  }
 

}

