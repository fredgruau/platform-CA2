package dataStruc

import compiler.AST
import dataStruc.DagNode.Neton

import scala.collection.{Iterable, immutable, mutable}

/**
 * Node of a Directed Acyclic Graph (DAG)
 * getCycle is used to test the absence of cycles
 * getGreater is used to collect all the nodes of a Dag,
 * whose set of minimum is passed or completed on the fly
 * neighbor is   an edge used with depth first search,
 * other is not an edge. It points to other nodes to explore the whole DAG
 * to complete on the fly an initial set of minimals
 */
trait DagNode[+T <: DagNode[T]] {
  //self: T =>
  def inputNeighbors: List[T]

  /** others are node that should be visited, but are not input neighbors.
   * by default there is none */
  def other: List[T] = List.empty

  /** we print without parenthesis when there is a single input */
  def toStringTree: String = toString + " " +
    (if (inputNeighbors.size > 1 || this.isInstanceOf[Neton[_]])
      "(" + inputNeighbors.map(_.toStringTree).foldLeft("")(_ + ", " + _).substring(2) + ")" //le substring vire la premiere virgule
    else if (inputNeighbors.size == 1) inputNeighbors.head.toStringTree else " ")

  /**
   * Tries to find a cycle
   *
   * @return the cycle if a cycle is found, else none
   */
  def getCycle: Option[Vector[T]] = new Dag[T]().dfs(this.asInstanceOf[T], Vector[T]())
}

/**
 * Contains trait that facilitates definitions of DagNodes, when the number of inputs is given to be 0,1,2,3 or arbirary
 */
object DagNode {

  trait EmptyBag[+T <: DagNode[T]] extends DagNode[T] {
    def inputNeighbors: List[T] = List.empty;
  }

  trait Singleton[+T <: DagNode[T]] extends DagNode[T] {
    def arg: T;

    def inputNeighbors: List[T] = List(arg)
  }

  trait Doubleton[+T <: DagNode[T]] extends DagNode[T] {
    def arg: T;

    def arg2: T;

    def inputNeighbors: List[T] = List(arg, arg2)
  }


  trait Tripleton[+T <: DagNode[T]] extends DagNode[T] {
    def arg: T;

    def arg2: T;

    def arg3: T;

    def inputNeighbors: List[T] = List(arg, arg2, arg3)
  }

  trait Neton[T <: DagNode[T]] extends DagNode[T] {
    def args: List[T];

    def inputNeighbors: List[T] = args
  }

}