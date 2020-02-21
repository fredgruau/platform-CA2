package compiler

import compiler.Constraint._

import scala.collection.immutable

//import scala.collection._
//import scala.collection._
import Align._
import scala.collection.immutable.{ArraySeq, HashSet}
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
sealed abstract class Constraint(val size:Int)
  {
    /** we must have checked partitionned before */
     def project(newSize:Int): Constraint
    /**The number of possible schedules.  */
  def card:Int
  /**Defined for constraint between a T component and an E/F component, if there is a unique possible T schedule, for each E (or each F) schedule 
   * it transforms an E or an F schedule into a T schedule*/
  def propagateFrom(a:Array[Int]):Option[Array[Int]]=None
    /** True if a is a possible schedule
     * @param a schedules to be checked */
    def verified(a:Seq[Int]):Boolean
  /**The new constraint after a permutation is applied to align to the root */
  def permute(p: Array[Int] ):Constraint
  def schedules: HashSet[Seq[Int]]
    /**   generate the schedules for the smallest card, and verify with the other.
     * unless specific cases where it can be deduced in a cheaper way */
  def intersect(c:Constraint):Constraint= {
    if(c.isInstanceOf[AllConstr] || (c==this)) this
    else if(c.card<card) c.intersect(this)    // c has smallest card
    else { val s= schedules
      val s2 =s.filter(c.verified(_))
      Schedules( HashSet.empty[Seq[Int]]++ s2,size)
    }
  }

    //Schedules(schedules.intersect(c.schedules))
    /** In general an isolated constraint has at least one schedules satifying it */
    def empty:Boolean=false
}

object Constraint {
  @scala.annotation.tailrec
  def factorial(n: Int, accum:  Int = 1):  Int =   if (n == 0)   accum   else    factorial(n - 1, n * accum)
  private def complement6(l:List[Int]): HashSet[Int] =   HashSet(0,1,2,3,4,5,6)--l
  private val simplic: Array[S]=Array(V(),V(),F(),E())

  final case class Schedules( b: HashSet[Seq[Int]] ,override val size:Int) extends Constraint(size){
    def card: Int =b.size
    def permute(p: Array[Int] ): Schedules =Schedules(b.map(_.map(p(_))),size)
    def schedules: HashSet[Seq[Int]] =b
   override def empty: Boolean = schedules.isEmpty
   override def verified(a: Seq[Int]): Boolean = b.contains(a)
  // override def toString: String ="mise a plat: "+b.toList.map(_.toList).mkString(",")
    override def project(newSize: Int): Constraint = Schedules(b.map(simplic(newSize).scheduleProj(_)),newSize)
  }
 // void constraint that incluces all schedules.
 final case class AllConstr(override val size:Int) extends Constraint(size){
   def card: Int = factorial(6)
   def permute(p: Array[Int] ): Constraint =this
   def schedules=  HashSet.empty[Seq[Int]]++ArraySeq(0,1,2,3,4,5).permutations
   override def intersect(c: Constraint): Constraint = c
   override def verified(a: Seq[Int]): Boolean = true
   override def project(newSize: Int): Constraint = AllConstr(newSize)

 }
  final case class BeginWithEither(b:List[Int] ,override val size:Int) extends Constraint(size){
    def card: Int =b.length*factorial(5)
    def permute(p: Array[Int] ): Constraint =BeginWithEither(b.map(p(_)),size)
    def schedules: HashSet[Seq[Int]] ={
      val u=b.map((x: Int) =>   complement6(List(x)).toList.permutations.map(x :: _)).flatten.map(_.toArray )
     // immutable.HashSet.empty[Seq[Int]] ++ b.map((x: Int) =>   complement6(List(x)).toList.permutations.map(x :: _)).flatten
      var S= HashSet.empty[Seq[Int]]
      for (t<-u) S=S+t
      S
    }
    override def verified(a: Seq[Int]): Boolean = return b.contains(a(0))
    override def project(newSize: Int): Constraint ={
      val s: immutable.HashSet[Int]=HashSet.empty++b.map(simplic(newSize).proj(_))
      BeginWithEither(s.toList,newSize)
    }
  }
    final case class Cycle(b:Seq[Int] ) extends Constraint(b.length){
    def card: Int =b.length //it depends where we starts. Cycles could go both direction, so we should multiply by two.  we consider just one, for "simplification"
    def permute(p: Array[Int] ): Constraint = Cycle(compose(b,p).toArray[Int])
      def schedules: HashSet[Seq[Int]] = {
        var c=b.toArray;var cycleLength=0
        var next =0
        val t:Array[Boolean]=Array(true,true,true,true, true,true)
        for(i<-0 to 5) { //intialisation of c needs to explore the (possibly numerous) cycles.
          c(i)=b(next); t(next)=false;   next=b(next)
          if(!t(next)){if(cycleLength==0) cycleLength=i+1   ;next=t.indexOf(true) }
        }
        var result= HashSet.empty[Seq[Int]]
  for (i <- 1 to b.length/cycleLength)   {val c2: Seq[Int] =c;result=result+c2;c=ASTL.rotR(c,cycleLength);}
  result;}
override def verified(a: Seq[Int]): Boolean =
{ val start= a. indexOf(b(0), 0)
  for(i<-0 to b.length-1) if(a((i+start)%a.length)!=b(i)) return false
  return true
}
  override def toString: String ="Cycle "+b.mkString(" ")
      override def project(newSize: Int): Constraint = Cycle( simplic(newSize).scheduleProj(b))
    }

  /** s is either an E or an F schedule upon creating the constraint,
   *  the constraint is valid for schedule such that in the image by b, the numbers get "not mixed" for exemple their can't be 010122, but 110022 is ok.
   *  b integrates the projection on the s, because it depends on the use of the simplicial field within the instruction
   *  */
    final case class Partition( b:Seq[Int],s:S) extends Constraint(size = 6){
  //  override def toString: String = "Partition "+s+" "+b.toSeq
    def card: Int =s.card
    def permute(p: Array[Int] ): Constraint =   Partition( compose(invert(p),b),s)
    def schedules: HashSet[Seq[Int]] = if (s.isInstanceOf[V]) AllConstr(1).schedules
      else  HashSet.empty ++ s.partitionnables.head.map( compose(_,b).toSeq)
    /** @param a represents a schedule of transfer, so it must be of size 6;
     *  @return  true if a can be partitionned on S,  */
    private def partitionable(a:scala.Seq[Int],s:S):Boolean={
      if  (s.isInstanceOf[V]) return true
      // val a2=compose(a,proj) //here we use proj, which is distinct for V,E and F
      //we check that values in a2 are "grouped"
      val alreadyMet =Array.fill[Boolean](s.card)(false)
      val res=Array.fill[Int](s.card)(0)
      var last = -1
      for (i<-0 to 5)
        if(a(i)!=last) {
          if (alreadyMet(a(i)) == true) return false // we just met a new index that was already met
          alreadyMet(a(i)) = true // register the fact that we start a zone.
          last = a(i)
        }
      return true
    }
    override def verified(a:  Seq[Int]): Boolean = partitionable(compose(a,b ),s ) //TODO a completer
    /** if it is alone, the Partition constraint does not constrain the simplicial type*/
    override def project(newSize: Int): Constraint = AllConstr(newSize)
  }

  object Partition {
    /** Used for testing partition of transfer variable which are reduced.  */
    def partOrAll(b:Seq[Int],s:S): Constraint= if(s.isInstanceOf[V]) AllConstr(6)  else  this(b,s)
    def partOrAll( s:S): Constraint= partOrAll(s.proj,s)
  }

      /** s is either an E or an F schedule upon creating the constraint, b must contain s.part at the beginning,
   *  the constraint is valid for schedule such that 
   *  1 after dividing by two for E (resp. by 3 for F) the image by b, 
   *  the numbers get "not mixed" for exemple their can't be 010122, but 110022 is ok.
   */ 

    final case class PartitionSucc( b:Array[Int],s:S) extends Constraint(size=6){
    def card: Int =s.cardSucc //it depends where we starts. Cycles could go both direction, so we should multiply by two.  we consider just one, for "simplification"
    
     def permute(p: Array[Int] ): Constraint =PartitionSucc(compose(invert(p),b) ,s)

    def schedules: HashSet[Seq[Int]] =null //TODO a completer
    override def propagateFrom(s2:Array[Int]):Option[Array[Int]]= s.propagateFrom(s2,b)
        override def verified(a: Seq[Int]): Boolean = false //TODO a completer
        /** we must have checked partitionned before */
        override def project(newSize: Int): Constraint = null //TODO finish
      }
  
   
  
}