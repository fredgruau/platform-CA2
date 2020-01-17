package compiler

import compiler.Constraint._

import scala.collection._
/** allows to delete evaluation of constraints: its either a set of Constraints, or a set of possible schedules (expressed constraints) */
trait Schedules {
  def isEmpty: Boolean
  /**needed to  align the constraint */
  def permute(p: Array[Int] ):Schedules
}

 
 
  /**
     * represent a set of possible schedule. a constraint linking Scc to Tcc (partition partitionSucc) must be able to take an Scc Schedule, 
     * and compute a set of Tcc Schedule complying with the constraint
     * Thereafter, find out if it has a non null intersection within the current constraint on the Tcc. 
     *It could also be done by taking a Tcc schedule, see if it check the partition, and if yes, compute the corresponding Scc schedule,
     *  however, in this case, one would
     *have to scan all the possible Tcc schedule, until we find one whose corresponding Scc schedule match our chosen schedule. 
     * If there is no constraint on the set of possible Tcc schedule, its size is the number of permutation: fact(6)
     */
sealed abstract class Constraint {
  /**The number of possible schedules.  */
  def card:Int
  /**Defined for constraint between a T component and an E/F component, if there is a unique possible T schedule, for each E (or each F) schedule 
   * it transforms an E or an F schedule into a T schedule*/
  def propagateFrom(a:Array[Int]):Option[Array[Int]]=None
  /**The new constraint after a permutation is applied to align to the root */
  def permute(p: Array[Int] ):Constraint
  def schedules:immutable.HashSet[Array[Int]]
  def intersect(c:Constraint):Constraint= Schedules(schedules.intersect(c.schedules))
}

object Constraint {
  def factorial(n: Int, accum:  Int = 1):  Int =   if (n == 0)   accum   else    factorial(n - 1, n * accum)
  def complement6(l:List[Int])=  immutable.HashSet(0,1,2,3,4,5,6)--l 
  
 final case class Schedules( b:immutable.HashSet[Array[Int]] ) extends Constraint{
    def card=b.size
    def permute(p: Array[Int] ): Schedules =Schedules(b.map(_.map(p(_))))
    def schedules=b
 
  }
 // private[Constraint]
  final case class BeginWithEither(b:List[Int] ) extends Constraint{
    def card=b.length*factorial(5)
    def permute(p: Array[Int] )=BeginWithEither(b.map(p(_)))
    def schedules=immutable.HashSet.empty[Array[Int]] ++ (b.map((x:Int)=> complement6(List(x)).toList.permutations.map(x::_)).flatten.map(_.toArray))
  }
    final case class Cycle(b:Array[Int] ) extends Constraint{
    def card=b.length //it depends where we starts. Cycles could go both direction, so we should multiply by two.  we consider just one, for "simplification"
    def permute(p: Array[Int] )=Cycle(b.map(p(_)))
     def schedules=immutable.HashSet(ASTL.rotR(b))
    override def toString="Cycle "+b.mkString(" ") }    
    
  /** s is either an E or an F schedule upon creating the constraint, b must contain s.part at the beginning,
   *  b contains 0,1,2 for E, O,1 for F. 
   *  the constraint is valid for schedule such that in the image by b, the numbers get "not mixed" for exemple their can't be 010122, but 110022 is ok.
   *  */
    final case class Partition( s:S, b:Array[Int]) extends Constraint{
    def card=s.card //it depends where we starts. Cycles could go both direction, so we should multiply by two.  we consider just one, for "simplification"
    def permute(p: Array[Int] )=Partition(s,b.map(p(_)))
    def schedules=null
    }    
      /** s is either an E or an F schedule upon creating the constraint, b must contain s.part at the beginning,
   *  the constraint is valid for schedule such that 
   *  1 after dividing by two for E (resp. by 3 for F) the image by b, 
   *  the numbers get "not mixed" for exemple their can't be 010122, but 110022 is ok.
   */ 

    final case class PartitionSucc(s:S ,b:Array[Int]) extends Constraint{
    def card=s.cardSucc //it depends where we starts. Cycles could go both direction, so we should multiply by two.  we consider just one, for "simplification"
    
     def permute(p: Array[Int] )=Partition(s,b.map(p(_)))
   
    def schedules=null
    override def propagateFrom(s2:Array[Int]):Option[Array[Int]]= s.propagateFrom(s2,b)
      
    }
  
   
  
}