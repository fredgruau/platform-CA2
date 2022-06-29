package dataStruc

import compiler.ASTB.Both
import compiler.ASTBfun.ASTBg
import compiler.Circuit.iTabSymb
import compiler.{AST, ASTB, Affect, Instr}

import scala.collection.{mutable, _}
import scala.collection.immutable.{HashMap, HashSet}


object Dag {
  def apply[T <: DagNode[T]]() = new Dag(List[T]())
  def apply[T <: DagNode[T]](g: List[T]) = new Dag(g)



}

/**
 * Represents an entire Directed acylic Graph
 *
 * @param generators optional initial generators
 * @tparam T
 */
class Dag[T <: DagNode[T]](generators: List[T]) {
  //TODO put all the fields in the constructor to avoid recomputing when transtlatin dag[Instr] into DagInstr

  /**
   * creates empty Dag
   */
  def this() = this(List())

  /** We create an exeption which can store the cycle
   * in order to be able to print it nicely later
   * nicely means with names  identifying fields in the client program */
  class CycleException(val cycle: Vector[T]) extends Exception("cycle is detected, depth increase from left to right\n" + cycle) {}


  /**   all the generators -maximal elements- from which all the other can be reached
   * TODO checks that elements in allGenerators are indeed maximal elements.
   * */
  var allGenerators: List[T] = List() //TODO maintain nonGenerator together with allGenerator, and forget visitedL
  /** @return non maximal dag's element */
  def nonGenerators(): List[T] = {
    val aG = HashSet.empty[AST[_]] ++ allGenerators
    visitedL.filter(!aG.contains(_))
  }

  /** all visited dag's node, are in topological order due to initial depth first search, (starting  with generators first) */
  var visitedL: List[T] = List()

  /** newly visited node */
  private var newVisitedL: List[T] = List()
  /** the set version of visitedL */
  private var visitedS: HashSet[T] = HashSet()
  addGreaterOf(generators) //visits all the Dag's nodes
  override def toString = allGenerators.map(_.toStringTree).mkString("\n")


  /**
   * add new generators to the Dag together with nodes which can be accessed from those.
   *
   * @param newGenerators generators possibly not in the DAG yet.
   * @return list of new node accessible from those newGenerators.
   *         TODO verifiez que c'est bien des générateurs
   */
  def addGreaterOf(newGenerators: List[T]): List[T] = {
    allGenerators ++= newGenerators
    //so that we can get which are the new nodes.
    newVisitedL = List()
    for (b <- newGenerators)
      dfs(b, Vector.empty) match {
        case Some(path) => throw new CycleException(path)
        case None =>
      }
    visitedL = newVisitedL ::: visitedL
    newVisitedL //returns newly visited nodes.
  }

  /**
   * adds to  visitedS  and visitedL, nodes reachable from n, using a depth first search (dfs)
   * if a cycle is generated, returns the corresponding path.
   * When we use case hierarchy, keys associated to distinct node, can be identical, and this subtelty
   * means that not all the nodes are visited, there is a single representant for each equivalence class.
   *
   * @param n        node to test
   * @param visiting nodes being checked for adding to visited.
   * @return option type with a cycle is there is one. starting and ending with the same element found at a deeper place
   */
  def dfs(n: T, visiting: Vector[T]): Option[Vector[T]] = {
    if (visitedS(n)) return None
    else if (visiting.contains(n))
      return Some((visiting).drop(visiting.indexOf(n)) :+ n)
    else {
      val visiting2 = visiting :+ n
      for (e <- n.inputNeighbors)
        dfs(e, visiting2) match {
          case Some(c) => return Some(c)
          case _ =>
        }
      visitedS = visitedS + n;
      newVisitedL = n :: newVisitedL
    }
    None
  }

  /** @param called input from outside usage which must also be counted
   * @return set of Dag's elements which are at least two times input to another dag's element
   *         we produce a set in order to be sure to eliminate doublon, we thus loose the order */
  def inputTwice(called: Seq[T] = Seq.empty[T]): Set[T] = {
    val all = (visitedL.flatMap(_.inputNeighbors) ++ called) //multiset with repetition
    val all2 = all.groupBy(identity)
    val nUser2 = immutable.HashMap.empty[T, Int] ++ all2.map { case (k, v) ⇒ k -> v.size } //computes multiplicity
    toSet(visitedL.filter(e => nUser2.contains(e) && nUser2(e) > 1)) //retains elements whose multiplicity is >=2
  }


  /**
   * if DagNodes  extend union wecan apply the unionFind algorithme to compute connected components .
   *
   * @param p predicate which defines adjacence beetween DagNodes
   * @result List of dagNodes of each component, as an iterable of iterable
   */
  def components2(p: (T, T) => Boolean): Iterable[List[T]] = {
    case class Wrap(elt: T) extends Union[Wrap]
    val all = immutable.HashMap.empty[T, Wrap] ++ visitedL.map(x => x -> Wrap(x))
    for (src <- visitedL) for (target <- src.inputNeighbors) if (p(src, target)) all(src).union(all(target)) //computes a common root for elements of one component
    visitedL.groupBy(all(_).root).values
  }

}




