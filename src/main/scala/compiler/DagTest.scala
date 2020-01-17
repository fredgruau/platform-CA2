package compiler

import junit.framework.TestCase

import junit.framework.Assert.assertEquals

class  DagTest  extends TestCase {
  
 /** A node of a DAG for testing cycles implemented as a Bag of neighbors
 *  @constructor create a node with neighbors and a name
 *  @param neighbors  passed by name for delaying evaluation
 *  @param name for printing purpose
 */
   class Node(  neighbors : => List[Node],val name:String) extends Dag[Node]    {
     def neighbor=neighbors;
     override def toString=name;
     def this( name:String)=this( List.empty,name)
     def this( name:String,e : =>  Node )=this( List(e),name)
       }
   val n1=new Node("n1");  val n2=new Node("n2");  val n3=new Node(List(n1,n2) ,"n3")
   def testGetGreater= { val(_, s)=Dag.getGreater( List(n3)); assertEquals(s, Set(n1,n2,n3))}
  val n4=new Node( "n4",n5)  //list n5 sera évalué plus tard
  val n4bis:Node=new Node( "n4bis",n4);   lazy val n5=new  Node(List(n1,n4bis) ,"n5")
  val n6=new Node( "n6",n4bis)
  def testGetCycle=  assert (Dag.getCycle(n4) match {case Some(c) => {println(c);true}; case None => false  })
}

  