package dataStruc

import compiler.AST.Read
import compiler.ASTB.AffBool
import compiler.{AST, ASTB, Affect, InfoType}
import compiler.Circuit.TabSymb
import dataStruc.Util.{radicalOfVar, radicalOfVar2}
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

  def isShift(s: String) = s.equals("<<") || s.equals(">>>")

  /** returns either the second neighbor or the value 1. */
  private def neighbor1or1(t: TabSymb[InfoType[_]]) = if (isShift(toString)) " 1" else inputNeighbors(1).toStringTreeInfixPar(t)

  /** * @param t symbol Table needed to check if variable is a parameter
   *
   * @return code of boolean instruction, adds a [i] if isParam is true, or i-1 if result parameter of radius 1
   */
  def toStringParam(t: TabSymb[InfoType[_]]): String = {
    if (t != null) if (isInstanceOf[AST[_]])
      this.asInstanceOf[AST[_]] match {
        case Read(name) => val rad = radicalOfVar2(name)
          if (t(rad).k.isParam || t(rad).k.isLayerField)
          return name + "[i]"
        case ASTB.AffBool(name, _) =>
          val nameRad = radicalOfVar2(name)
          if (t(nameRad).k.isParam)
            if (t(nameRad).k.isRadius1)
              return name + "[i-1]=" //Radius can be either 0 or 1
            else return name + "[i]="
        case _ => toString
      };
    toString
  }


  def toStringTreeInfix(t: TabSymb[InfoType[_]]): String = {
    assert {
      inputNeighbors.size <= 2
    }
    if (inputNeighbors.size == 2 || (inputNeighbors.size == 1 && isShift(toString)))
      inputNeighbors.head.toStringTreeInfixPar(t) + " " + toString + " " + neighbor1or1(t)
    else " " + toStringParam(t) + " " + (if (inputNeighbors.size == 1) inputNeighbors.head.toStringTreeInfix(t) else " ")
  }

  private def toStringTreeInfixPar(t: TabSymb[InfoType[_]]): String = {
    assert {
      inputNeighbors.size <= 2
    }
    if (inputNeighbors.size == 2 || (inputNeighbors.size == 1 && isShift(toString)))
      "(" + inputNeighbors.head.toStringTreeInfixPar(t) + " " + toString + " " + neighbor1or1(t) + ")"
    else " " + toStringParam(t) + " " + (if (inputNeighbors.size == 1) inputNeighbors.head.toStringTreeInfix(t) else " ")
  }

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