package compiler

import dataStruc.DagNode._
import dataStruc.{DagNode, Union}
import org.scalatest.FunSuite

class ConnectedCompTest extends FunSuite{
   /** A node of a DAG for testing cycles implemented as a Bag of neighbors
 *  @constructor create a node with neighbors and a name
 *  @param neighbors  passed by name for delaying evaluation
 *  @param name for printing purpose
 */
   class Node(  neighbors : => List[Node],val name:String) extends DagNode[Node] with Union[Node]   {
     def inputNeighbors: List[Node] =neighbors
     override def toString: String =name
     def this( name:String)=this( List.empty,name)
     def this( name:String,e : =>  Node )=this( List(e),name)
       }

  val n1=new Node("n1") with Union[Node]   ;  val n2=new Node ("n2") with Union[Node]  ;  val n3=new Node (List(n2) ,"n3") with Union[Node]  
  val cc=  components(List(n1,n2,n3), (_:Node, _:Node)=> true)
    print(cc)  
   test("components") {assert (cc.size===2)} //two connected components.
   
}
