package compiler


import compiler.AST.Layer
import compiler.ASTL.{IntV, delayedL}
import dataStruc.{Dag, DagNode}
import org.scalatest.{BeforeAndAfter, FunSuite}

class DagTest extends FunSuite with BeforeAndAfter {

  /** A node of a DAG for testing cycles implemented as a Bag of neighbors
   *
   * @constructor create a node with neighbors and a name
   * @param neighbors passed by name for delaying evaluation
   * @param name      for printing purpose
   */
   class Node(  neighbors : => List[Node],val name:String) extends DagNode[Node]    {
     def inputNeighbors: List[Node] = neighbors

   override def toString: String = name

   def this(name: String) = this(List.empty, name)

   def this(name: String, e: => Node) = this(List(e), name)
 }

  val n1 = new Node("n1");
  val n2 = new Node("n2");
  val n3 = new Node(List(n1, n2), "n3")
  test("addGreaterOfGenerators") {
    //val (_, s) = DagNode.getGreater(List(n3)); assert(s === Set(n1, n2, n3))
    val d = Dag[Node]()
    val inputn3 = d.addGreaterOf(List(n3))
    assert(inputn3.toSet === Set(n1, n2, n3))
  }
  val n4 = new Node("n4", n5) //list n5 sera évalué plus tard
  val n4bis: Node = new Node("n4bis", n4);
  lazy val n5 = new Node(List(n1, n4bis), "n5")
  val n6 = new Node("n6", n4bis)
  test("GetcycleDagSimple") {
    assert(n4.getCycle match { case Some(c) => println("there is a cycle: " + c); true; case None => false })
  }

  /** Builds a cycle in the DAG */
  class CycleLayer2(nbit: Int)(implicit m: repr[V]) extends Layer[(V, SI)](nbit) with ASTLt[V, SI] {
    lazy val x: IntV = next + pred.asInstanceOf[ASTLt[V, SI]]
    val next: ASTLt[V, SI] = delayedL(x)
  }

  val testCycle: Circuit[V, SI] = new Circuit[V, SI]() {
    val chip = new CycleLayer2(3);

    def computeRoot: ASTLt[V, SI] = chip.next
  }

  test("GetcycleDagAst") {
    try {
      testCycle.compile(Circuit.hexagon)
      assert(false)
    } //if no exeption is raised, test fails.
    catch {
      case e@(_: RuntimeException | _: java.io.IOException) => println(e)
    }
  }

}

