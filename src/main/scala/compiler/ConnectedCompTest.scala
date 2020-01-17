package compiler

import compiler.Dag._
import junit.framework.TestCase

class ConnectedCompTest extends TestCase{ 
   /** A node of a DAG for testing cycles implemented as a Bag of neighbors
 *  @constructor create a node with neighbors and a name
 *  @param neighbors  passed by name for delaying evaluation
 *  @param name for printing purpose
 */
   class Node(  neighbors : => List[Node],val name:String) extends Dag[Node] with Union[Node]   {
     def neighbor=neighbors;
     override def toString=name;
     def this( name:String)=this( List.empty,name)
     def this( name:String,e : =>  Node )=this( List(e),name)
       }
   
    
  val n1=new Node("n1") with Union[Node]   ;  val n2=new Node ("n2") with Union[Node]  ;  val n3=new Node (List(n2) ,"n3") with Union[Node]  
 
  //val n1=new Node("n1")    ;  val n2=new Node ("n2")   ;  val n3=new Node (List(n2) ,"n3")   
   val cc=  components(List(n1,n2,n3), (x:Node,y:Node)=> true)
    print(cc)  
    def testCC=  assert (cc.size==2) //two connected components. 
   
}
