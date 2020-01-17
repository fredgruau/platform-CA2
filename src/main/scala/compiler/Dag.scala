package compiler

import scala.collection._
import scala.collection.mutable.LinkedHashMap
 
/**
 * Node of a directed acyclic graph
 * getCycle is used to test the absence of cycles
 * getGreater is used to collect all the nodes of a Dag,
 *  whose set of minimum is passed or completed on the fly
 * neighbor is   an edge used with depth first search,
 * other is not an edge. It points to other nodes to explore the whole DAG
 *     to complete on the fly an initial set of minimals
 */
trait Dag[T <: Dag[T]] {
  def neighbor: List[T]
  /**by default there is no new fiedls to visit */
  def other: List[T] = List.empty
  def toStringTree: String = toString + " " +
    (if (neighbor.size > 1 || this.isInstanceOf[AST.Neton[_]]) "(" + (neighbor.map(_.toStringTree)).foldLeft("")(_ + ", " + _).substring(2) + ")" //le substring vire la premiere virgule
    else if (neighbor.size == 1) neighbor.head.toStringTree else " ")
}

object Dag {
  /**
   * Used to instanciate a hashset "visited" of the right type T <: Dag[T]
   */

  class Dfs[T <: Dag[T]](var visited: immutable.HashSet[T]) {
    def this() = this(immutable.HashSet.empty[T] )
    /**VisitedL is used to preserve the order */
    var visitedL: List[T] = List.empty;
    /**
     * verify that there is no cycle within a graph, starting from a given node n
     * using a depth first search (dfs)
     * simultaneously update visited which contains all the node that can be reached from b
     * @n  node to test
     * @return option type with a cycle is there is one.
     */
    def dfs(n: T, visiting: Vector[T]): Option[Vector[T]] = {
      if (visited(n)) return None
      else if (visiting.contains(n))
        return Some(visiting.drop(visiting.indexOf(n) - 1))
      else {
        val visiting2 = visiting :+ n;
        for (e <- n.neighbor)
          dfs(e, visiting2) match { case Some(c) => return Some(c) case _ => }
        visited = visited + n
        visitedL = n :: visitedL
        //visit "other" nodes met on the fly (in the next part of layers
        for (e <- n.other) if (!visiting.contains(e) && e != n)
          dfs(e, Vector.empty) match { case Some(c) => return Some(c) case _ => }
      }
      return None
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
  def getGreater[T <: Dag[T]](minimals: List[T], visited:  immutable.HashSet[T]) =
    {
      val dfs = new Dfs[T](visited)
      for (b <- minimals)
        dfs.dfs(b, Vector.empty) match {
          case Some(path) => throw new RuntimeException("cycle detected in AST:" + path)
          case None       =>
        }
      (dfs.visitedL, dfs.visited);
    }

  def getGreater[T <: Dag[T]](minimals: List[T]): (List[T], immutable.HashSet[T]) = getGreater(minimals,  immutable.HashSet.empty[T])
  /**
   * Tries to find a cycle
   * @param n starting node to reach the cycle
   * @return the cycle if a cycle is found, else none
   */
  def getCycle[T <: Dag[T]](n: T): Option[Vector[T]] =
    { val dfs = new Dfs[T]; return dfs.dfs(n, Vector.empty) }

  /** Topological sort is done by finding minimals, and then visiting nodes starting  from minimals*/
  def sort[T <: Dag[T]](l: List[T]): List[T] = {
    //finds node with no incomming links:
    val withIncomming = immutable.HashSet.empty[T] ++ l.map(_.neighbor).flatten
    val noIncomming = (immutable.HashSet.empty[T] ++ l) -- withIncomming
    val (orderdNodes, visited1) = getGreater(noIncomming.toList)
    return (orderdNodes)
  }
  /**
   * computes the connected components the resulting partition is a kind of list of list, (iterable of Iterable)
   * The DAG must extends union so as to have the necessary private field myroot,rank,parent, plus the code of union.
   * @p  predicate defines adjacence
   */
  def components[T <: Dag[T] with Union[T]](all: List[T], p: (T, T) => Boolean): Iterable[Iterable[T]] = {
    for (src <- all) for (target <- src.neighbor) if (p(src, target)) src.union(target);
    val m = LinkedHashMap.empty ++ all.map(x => (x -> x.root)); // print(m)
    m.groupBy(_._2).map { case (k, v) => v.keys }  
  }  
 

}

