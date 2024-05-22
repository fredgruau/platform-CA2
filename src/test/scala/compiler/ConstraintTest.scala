package compiler

import Constraint.{AllConstr, Cycle, Partition, Schedules}
import org.scalatest.FunSuite

import scala.collection.immutable.{ArraySeq, HashSet}

class ConstraintTest extends FunSuite {

  test("testCycle") {
    val c:Constraint=Cycle(ArraySeq(1,2,3,4,5,0), T(V(),E()))
    // println(c)
    assert(c.verified(ArraySeq( 2,3,4,5,0,1)))
    val cs=Schedules(c.schedules,c.locus)
    assert(cs.card === 6)
    //printMem(cs)
  }

  test("testPartition") {
    val p=Partition(E().proj,E(),T (E(),V()))
    println("totototo"+p.schedules)
    println("tatatata"+p.schedules)
    val sched=ArraySeq(0,1,2,3,4,5)
    val sched2=ArraySeq(0, 1, 2)
    assert(p.verified(sched))
    val toE  = Constraint.propagate(p,Schedules(HashSet(sched), T (E(),V() ))) //testing propagation of schedule from vE to E
    assert  ( toE.schedules===HashSet(sched2))
    assert(Constraint.propagate(p,p)===AllConstr(E())) //propagated partition does not constraint simplicial
    val tovE =  Constraint.propagate(p,Schedules(HashSet(sched2), E())) //this time we propagate from E to vE
    assert(tovE.verified(sched))  //sched is a possible schedules.
    //val picked=tovE.pick() ; println(picked)

   // val picked=p.pick() ; println(picked)

  }



}
