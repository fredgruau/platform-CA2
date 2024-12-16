package sdn
import compiler.AST.Layer
import compiler.ASTBfun.{derivative, orScan}
import compiler.SpatialType.{UintV, _}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.hexagon
import compiler._
import compiler.SpatialType._
import dataStruc.{BranchNamed, Named}
import sdn.{BlobE, BlobV, BlobVe, HasBrdE, HasBrdVe, MuStruct}
import progOfmacros.Comm._
import progOfmacros.Topo.brdin
import progOfmacros.{Grad, Wrapper}
import progOfmacros.Util.{randE2, randN12, randNext}
import progOfmacros.Wrapper.{borderS, existS, not, segment1, shrink}
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
/** same as Compar, except that we compare apex neighbors instead of direct neighbors? */
trait ComparApex{
  self:UintV=>
val ef=apexEui(f(this))
  /** xor can be usefull for other things, so we keep a pointer to it */
  val bordApex: UintE =Wrapper.border[F,E,UI](ef)
  //val bord: UintE =Wrapper.border[V,E,UI](dEv) //a déja calculé dev.
  /**  usefull both for lt, and for eq a single bit is on, iff operand on each edge side differ */
  val segmentOf1Apex: UintE = segment1(bordApex) //unop(orScan, bord)
  /** true if both values are different */
  val diffApex= elt(0,segmentOf1Apex)
  /** true if both values are equal */
  val eqApex= not(diffApex);
  val ltApex=Grad.ltApex(this,segmentOf1Apex)
  val gtApex=symEf(ltApex)
}

trait Compar{
  self:UintV=>
  //var delay: ASTLt[V, UI] =delayedL(this)"3"

  /** xor can be usefull for other things, so we keep a pointer to it */
  val bord: UintE =Wrapper.borderS[V,E,UI](this)
  //val bord: UintE =Wrapper.border[V,E,UI](dEv) //a déja calculé dev.
  /**  usefull both for lt, and for eq a single bit is on, iff operand on each edge side differ */
  val segmentOf1: UintE = segment1(bord) //unop(orScan, bord)
  /** true if both values are different */
  val diff= elt(0,segmentOf1)
  /** true if both values are equal */
  val eq= not(diff);
  val lt=Grad.lt(this,segmentOf1)
  val gt=symEv(lt)
}

/** add a boolVf that computes lt with respect to the three neibors of the adjacent face, using an And transfer reduction redT*/
trait Compar3 {
  self: UintV with Compar =>
  val lt3:BoolVf=shrink(transfer(lt))
}
/** contains addxxxx(arg) function which managas to add the functionality xxx to the argument arg */
object Util {
  /** return an unsigned vertex random integer of $n$ bits */
  def randUintV(nbits: Int): UintV = {
    Array.fill(nbits)(root4naming.addRand()).reduce(_ :: _)  //all the random bits get concatenated.
    //pb: quand ya un seul bit, ya pas de concat, et ca renvoie un boolV
  }

  /** we directly re use Delayedc reation, in order to be able to add  COmparison operators,
   * this naming will automatically define trucLt, trucEq, trucGt, trucLe, trucGe*/
  def addLt(_arg: => UintV): UintVx = {// with Compar with ComparApex with Compar3
    lazy val delayed = _arg;
    new AST.Delayed[(V, UI)](() => delayed) with ASTLt[V, UI] with Compar with ComparApex  with Compar3 with Named with BranchNamed {}
  }

  /** we directly reuse Delayed creation, in order to be able to add  blob related computation,
   * this naming will automatically define meetV,meetE, BrdV, BrdE*/
  def addBlobV(_arg: => BoolV): Blob = {
    lazy val delayed = _arg;
    new AST.Delayed[(V, B)](() => delayed) with BoolV with BlobV with Named with BranchNamed {}
  }

  /** we directly reuse Delayed creation, in order to be able to add  blob related computation, on a BoolE
   * this naming will automatically define meetV,meetE, BrdV, BrdE*/
  def addBlobE(_arg: => BoolE):Blob = {// with Compar with ComparApex with Compar3
    lazy val delayed = _arg;
    new AST.Delayed[(E, B)](() => delayed) with BoolE with BlobE with Named with BranchNamed {override val brdE: BoolE = delayed}
  }
  /** we directly reuse Delayed creation, in order to be able to add  blob related computation on a BoolVe,
   * this naming will automatically define meetV,meetE, BrdV, BrdE*/
  def addBlobVe(_arg: => BoolVe):Blob = {// with Compar with ComparApex with Compar3
    lazy val delayed = _arg;
    new AST.Delayed[(T[V,E], B)](() => delayed) with BoolVe with BlobVe with Named with BranchNamed {override val brdVe: BoolVe = delayed}
  }

  /**
   *
   * @param b represent a boolV offering computation of meeting points
   * @return places where growig will not cause merging of blobs.
   */
  def safeGrow(b:Blob):BoolV={
    val meetEside = existS[E, V](b.meetE) //true if adjacent to a meeting edge
    val meet = b.meetV | meetEside //  all meeting Vertices
    b.brdV & ~meet
  }







    {}



}

/** Layer implementing a random bit */
class Rand() extends Layer[(V, B)](1, "random") with ASTLt[V, B]         {
  val next: BoolV = randNext(this) //randDef is used only here, no need for a wrapper!
  lazy val randDir: BoolVe = randN12(this) //lazy because probably not used
  lazy val randSide: BoolEv = randE2(this) //only qpointRand uses this
}

