package dataStruc

import compiler.ASTB.Both
import compiler.ASTBfun.ASTBg
import compiler.Circuit.iTabSymb
import compiler.{AST, ASTB, Affect, Instr}

import java.lang
import java.lang.System
import scala.Console.out
import scala.collection.{Map, mutable, _}
import scala.collection.immutable.{HashMap, HashSet, ListSet}


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

  /** @return non maximal dag's element, assuming maximals have been stored in allGenerators. */
  def nonGenerators(): List[T] = {
    val aG = HashSet.empty[T] ++ allGenerators
    visitedL.filter(!aG.contains(_))
  }

  /** all visited dag's node, are in topological order due to initial depth first search, (starting  with generators first) */
  var visitedL: List[T] = List()

  /** newly visited node */
  private var newVisitedL: List[T] = List()
  /** the set version of visitedL */
  private var visitedS: Set[T] = ListSet()
  addGreaterOf(generators) //visits all the Dag's nodes
  def toStringOld = allGenerators.map(_.toStringTree).mkString("\n")

  override def toString: String = // "there is " + visitedL.length + " DagNodes\n" +
    visitedL.reverse.map((i: DagNode[T]) => i.toString()).mkString("")

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
        case Some(path) =>
          throw new CycleException(path)
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
   * Adds attributes allowing to compute the union find algorithm
   *
   * @param elt
   */
  case class Wrap(elt: T) extends Union[Wrap]

  /**
   * we apply the unionFind algorithme to compute connected components .
   *
   * @param testCycle true if we want to avoid cycles
   * @param p   predicate which defines adjacence beetween DagNodes
   * @param myWrap    mapping associating an element to its wrapping. itcan be provided by the calling environment, it it needs it
   * @result map associating a root to its component
   *         TODO redefinir a partir de indexed paquet
   */


  def indexedComponents(p: (T, T) => Boolean, testCycle: Boolean, myWrap: Map[T, Wrap] = immutable.HashMap.empty[T, Wrap] ++ visitedL.map(x => x -> Wrap(x))): Map[T, List[T]] = {
    /** at the beginning, all the elements are roots. */

    var intputNeighborRoots: Map[T, Set[T]] = null;
    if (testCycle)
      intputNeighborRoots = immutable.HashMap.empty ++ visitedL.map(x => x -> x.inputNeighbors.toSet)

    def inputNeihborRootsClosure(t: T): Set[T] = {
      var result: Set[T] = intputNeighborRoots(t)
      for (input <- intputNeighborRoots(t))
        result = result.union(inputNeihborRootsClosure(input))
      result
    }

    def inputNeihborRootsClosures(ts: Set[T]): Set[T] = if (ts.isEmpty) HashSet.empty else
      ts.map(inputNeihborRootsClosure(_)).reduce((x, y) => x.union(y))

    /** a cycle is created if src contains trueInputNeighborsClosure from neighbors other than target, which contains target */
    def cycleCreation(src: T, target: T) = {
      val r = inputNeihborRootsClosures(src.inputNeighbors.toSet - target).contains(target)
      if (r) System.out.println("" + src + "annnnd" + target + "create a cycle")
      r
    }


    for (src: T <- visitedL)
      for (target <- src.inputNeighbors)
        if (p(src, target) && (!testCycle || !cycleCreation(src, target))) { //either we accept cycle, or we do not but there is none

          val rootoRemove = myWrap(src).union(myWrap(target)) //in case of a true union, we need to know which root is removed
          val newCommonRoot: T = myWrap(src).root.elt //computes a common root for elements of one component
          if (testCycle)
            rootoRemove match {
              case None => //the two merged nodes already add the same root, so nothing needs to be done.
              case Some(r) => //root r, is removed

                intputNeighborRoots = intputNeighborRoots + (newCommonRoot ->
                  (intputNeighborRoots(newCommonRoot) - r.elt).union(intputNeighborRoots(r.elt)))
                intputNeighborRoots = intputNeighborRoots - r.elt
                val u = 0
            }
        }
    visitedL.groupBy(myWrap(_).root.elt)
  }


  /**
   * we apply the unionFind algorithm to compute connected components .
   *
   * @param p   predicate which defines adjacence beetween DagNodes
   * @param all mapping associating an element to its wrapping. itcan be provided by the calling environment, it it needs it
   * @result List of dagNodes of each component, as an iterable of iterable
   */
  def components2(p: (T, T) => Boolean, all: Map[T, Wrap] = immutable.HashMap.empty[T, Wrap] ++ visitedL.map(x => x -> Wrap(x))): Iterable[List[T]] =
  {
    indexedComponents(p, false, all).values
  }

}


