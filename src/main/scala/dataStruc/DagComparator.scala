package dataStruc
import scala.collection.mutable

object DagComparator {

  // Topological Sort using Kahn's Algorithm
  def topologicalSort(graph: Map[Int, List[Int]], numNodes: Int): List[Int] = {
    val indegree = Array.fill(numNodes)(0)
    graph.foreach { case (_, neighbors) => neighbors.foreach(v => indegree(v) += 1) }

    val queue = mutable.Queue[Int]()
    for (i <- indegree.indices if indegree(i) == 0) queue.enqueue(i)

    val topoOrder = mutable.ListBuffer[Int]()
    while (queue.nonEmpty) {
      val node = queue.dequeue()
      topoOrder += node
      for (neighbor <- graph.getOrElse(node, List())) {
        indegree(neighbor) -= 1
        if (indegree(neighbor) == 0) queue.enqueue(neighbor)
      }
    }
    topoOrder.toList
  }

  // Compute reachability using the topological order
  def computeReachability(graph: Map[Int, List[Int]], numNodes: Int): Array[Set[Int]] = {
    val topoOrder = topologicalSort(graph, numNodes)
    val reachable = Array.fill(numNodes)(mutable.Set[Int]())

    for (node <- topoOrder.reverse) {
      for (neighbor <- graph.getOrElse(node, List())) {
        reachable(node) += neighbor
        reachable(node) ++= reachable(neighbor)  // Add all nodes reachable from `neighbor`
      }
    }
    reachable.map(_.toSet)  // Convert to immutable sets
  }

  // Check if two nodes are comparable and return the greater node if they are
  def isComparable(reachable: Array[Set[Int]], u: Int, v: Int): (Boolean, Option[Int]) = {
    if (reachable(u).contains(v)) (true, Some(u))    // u > v
    else if (reachable(v).contains(u)) (true, Some(v)) // v > u
    else (false, None)                                // Not comparable
  }

  // Example usage
  def main(args: Array[String]): Unit = {
    // Define graph as adjacency list
    val numNodes = 5
    val graph = Map(
      0 -> List(1),
      1 -> List(2, 3),
      3 -> List(4)
    )

    // Precompute reachability
    val reachable = computeReachability(graph, numNodes)

    // Query for comparability
    val (u, v) = (1, 3)
    val (comparable, greater) = isComparable(reachable, u, v)
    if (comparable) println(s"Nodes $u and $v are comparable. Node ${greater.get} is greater.")
    else println(s"Nodes $u and $v are not comparable.")
  }
}
