package dataStruc

import compiler.AST
import dataStruc.DagNode.Dfs

import scala.collection.immutable.HashSet
import scala.collection.{mutable, _}
 
/**
 * Node of a Directed Acyclic Graph (DAG)
 * getCycle is used to test the absence of cycles
 * getGreater is used to collect all the nodes of a Dag,
 *  whose set of minimum is passed or completed on the fly
 * neighbor is   an edge used with depth first search,
 * other is not an edge. It points to other nodes to explore the whole DAG
 * to complete on the fly an initial set of minimals
 */
trait DagNode[T <: DagNode[T]] {
  def inputNeighbors: List[T]
  /**others are node that should be visited, but are not input neighbors. by default there is none */
  def other: List[T] = List.empty
  def toStringTree: String = toString + " " +
    (if (inputNeighbors.size > 1 || this.isInstanceOf[AST.Neton[_]]) "(" + inputNeighbors.map(_.toStringTree).foldLeft("")(_ + ", " + _).substring(2) + ")" //le substring vire la premiere virgule
    else if (inputNeighbors.size == 1) inputNeighbors.head.toStringTree else " ")
}

/**
 * Represents an entire Directed acylic Graph
 *
 * @tparam T
 */
class Dag[T <: DagNode[T]]( ){
  /** already visited nodes */
   private val dfs = new Dfs[T]
  /**  generators represent the element from which all the other can be reached.*/
  var generators:List[T]= List()
  var visitedL:List[T]= List()
  var visited:HashSet[T]= HashSet()
  override def toString=generators.map(_.toStringTree).mkString("\n")

  /**
   * @param newGenerators other nodes possibly not in the DAG yet, which need to be expored.
   * @return list of new node added from those newGenerators.
   */
  def addGenerators( newGenerators:List[T]): List[T] ={
    generators=newGenerators++generators
    dfs.resetVisitedL() //so that we can get which are the new nodes.
    for (b <- newGenerators)
      dfs.dfs(b, Vector.empty) match {
        case Some(path) => throw new RuntimeException("cycle detected in AST:" + path)
        case None       =>
      }
    visited=dfs.visited
    visitedL=dfs.visitedL:::visitedL
    dfs.visitedL //returns newly visited nodes.
  }
}

object DagNode {
  /**
   *
   * Depth First Search, Used to instanciate a hashset "visited" of the right type T <: Dag[T]
   * @param visited hashset of visited nodes, allways augment
   * @tparam T Node of Dag
   */

  class Dfs[T <: DagNode[T]](var visited: immutable.HashSet[T]) {
    def this() = this(immutable.HashSet.empty[T] )
    /**VisitedL is a list version of visited,  used to preserve the order of visit */
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
        //for (e <- n.other) if (!visiting.contains(e) && e != n)
        //  dfs(e, Vector.empty) match { case Some(c) => return Some(c) case _ => }
      }
      None
    }
  }
  /**
   *
   * Depth First Search, Used to instanciate a hashset "visited" of the right type T <: Dag[T]
   * @param visited hashset of visited nodes, allways augment
   * @tparam T Node of Dag
   */

   class DfsOld[T <: DagNode[T]](var visited: immutable.HashSet[T]) {
    def this() = this(immutable.HashSet.empty[T] )
    /**VisitedL is a list version of visited,  used to preserve the order of visit */
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
   * Tries to find a cycle
   * @param n starting node to reach the cycle
   * @return the cycle if a cycle is found, else none
   */
  def getCycle[T <: DagNode[T]](n: T): Option[Vector[T]] =
    { val dfs = new DfsOld[T]; dfs.dfs(n, Vector.empty) }
/*
  /** Topological sort is done by finding minimals, and then visiting nodes starting  from minimals
  this is bugged, because getGreater starts with the node without outcoming, not without incomming
 */
  def sort[T <: Dag[T]](l: List[T]): List[T] = {
    //finds node with no incomming links:
    val withIncomming = immutable.HashSet.empty[T] ++ l.flatMap(_.inputNeighbors)
    val noIncomming = (immutable.HashSet.empty[T] ++ l) -- withIncomming
    val (orderdNodes, _) = getGreater(noIncomming.toList)
    orderdNodes
  }*/
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

