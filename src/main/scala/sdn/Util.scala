package sdn
import compiler.SpatialType._
import compiler.AST._
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.hexagon
import compiler._
import compiler.SpatialType._
import dataStruc.{BranchNamed, Named}
import progOfCA.MuStruct
import progOfmacros.Grad
import progOfmacros.Util.{randE2, randN12, randNext}
import sdn.Globals.{root4naming, setRoot4naming}

import scala.::
import scala.collection.mutable

/** contains method and data  system wide,relevant  */
object Globals{
  /**fields in root4naming is garante to get a name from the reflection naming algo */
  var root4naming:Root4naming=null
  /** to be called by  the root Agent*/
 def setRoot4naming(a:Root4naming)={
   root4naming=a
 }
}

/** used to break a cycle in defining a root4namming.
 *  Also contains stuff that needs to get a name such as the rand bits which are layers (layers should get a name)
 *  more generally, root4naming will contains system wide method and data, accessible everywhere, through the object Global.
 *  */
class Root4naming() extends Named with BranchNamed{
  setRoot4naming(this)
  /** setting of encapsulated muStruct  is delayed, otherwise dependency cycle is still holding , so we use a var for n.*/
  var n:Named=null
  /** set encapsulated muStruct */
  def setRootMustruct(n2:Named)={
    n=n2
    n.setName("") //this will artificially remove a level "N" in the hierarchy of printed fields
  }
  /** random bits  are stored in a mutable hashmap*/
  val rands=new mutable.HashMap[Int,UintV]() with Named{}
  /** adds a random boolean bit, which will be named */
  def addRand(): UintV ={
    val res=new Rand().asInstanceOf[UintV]
    rands(rands.size)=res //add a new random bits to the already existing, its index is just the hashmap size
    res //random bit is returned
  }
}

trait Compar{
  self:UintV=>
  val (lt,eq)=Grad.slopeLt(delayedL( this)) //voir si on peut enlever ce delayed, quand meme.
}

object Util {
  /** return an unsigned vertex random integer of $n$ bits */
  def randUintV(nbits: Int): UintV = {
    Array.fill(nbits)(root4naming.addRand()).reduce(_ :: _)  //all the random bits get concatenated.
    //pb: quand ya un seul bit, ya pas de concat, et ca renvoie un boolV
  }

  /** delayedL reprograms delayed, in order to add the trait ASTLt[L, R] */
  def addLt(_arg: => UintV):UintV with Compar= {
    lazy val delayed = _arg;
    new Delayed[(V, UI)](() => delayed) with ASTLt[V, UI] with Compar with Named with BranchNamed {}

  }
}

/** Layer implementing a random bit */
class Rand() extends Layer[(V, B)](1, "random") with ASTLt[V, B]         {
  val next: BoolV = randNext(this) //randDef is used only here, no need for a wrapper!
  lazy val randDir: BoolVe = randN12(this) //lazy because probably not used
  lazy val randSide: BoolEv = randE2(this) //only qpointRand uses this
}


