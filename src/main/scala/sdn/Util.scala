package sdn
import compiler.AST.{Call1, Layer}
import compiler.ASTBfun.{derivative, orScan}
import compiler.SpatialType.{UintV, _}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.ASTLt.ConstLayer
import compiler.Circuit.hexagon
import compiler._
import compiler.SpatialType._
import dataStruc.{BranchNamed, Named}
import sdn.{BlobE, BlobV, BlobVe, HasBrdE, HasBrdVe, MuStruct}
import progOfmacros.Comm._
import progOfmacros.Topo.brdin
import progOfmacros.{Grad, Wrapper}
import progOfmacros.Util.{randE2, randN12, randNext, torusify}
import progOfmacros.Wrapper.{borderS, enlarge, existS, not, segment1,  shrink}
import sdn.Globals.{root4naming, setRoot4naming}

import scala.::
import scala.collection.mutable

/** contains method and data for programming self development,  relevant system wide,  */
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
class Root4naming() extends Named with BranchNamed {
  setRoot4naming(this)
  /** setting of encapsulated muStruct  is delayed, otherwise dependency cycle is still holding , so we use a var for n. */
  var n: Named = null

  /** set encapsulated muStruct */
  def setRootMustruct(n2: Named) = {
    n = n2
    //n.setName("") //this will artificially remove a level "N" in the hierarchy of printed fields
  }

  /** random bits  are stored in a mutable hashmap */
  val rands = new mutable.HashMap[Int, UintV]() with Named {}

  /** adds a random boolean bit, which will be named */
  def addRandBit(): UintV = {
    val res = new Rand().asInstanceOf[UintV]
    rands(rands.size) = res //add a new random bits to the already existing, its index is just the hashmap size
    res //random bit is returned
  }

  def addConstRandBit(): BoolV = {
    val res = new ConstLayer[V, B](1, "random")
    rands(rands.size) = res.asInstanceOf[UintV] //add a new random bits to the already existing, its index is just the hashmap size
    res //random bit is returned
  }
}

trait ComparSI{
  self:SintV=>
  val bord: SintE =Wrapper.borderS[V,E,SI](this)
  val segmentOf1: SintE = segment1(bord) //unop(orScan, bord)
  /** true if both values are different */
  val diff= elt(0,segmentOf1)
/** true if both values are equal*/
val eq= not(diff);
}

/** computes lt, gt, eq*/
trait Compar{
  self:UintV=>
  /** xor can be usefull for other things, so we keep a pointer to it, it is an UintE which stores the difference */
  val bord: UintE =Wrapper.borderS[V,E,UI](this)
  //val bord: UintE =Wrapper.border[V,E,UI](dEv) //a déja calculé dev.
  /**  usefull both for lt, and for eq. a single bit is on, iff operand on each edge side differ */
  val segmentOf1: UintE = segment1(bord) //unop(orScan, bord)
  /** true if both values are different */
  val diff= elt(0,segmentOf1)
  /** true if both values are equal */
  val eq= not(diff);
  val lt: BoolEv =Grad.lt(this,segmentOf1)
  val gt=symEv(lt)
}
/** same as Compar, except that we compare apex neighbors instead of direct neighbors? */
trait ComparApex{
  self:UintV=>
  val ef: UintEf =apexEui(f(this))
  /** xor can be usefull for other things, so we keep a pointer to it */
  val bordApex: UintE =Wrapper.border[F,E,UI](ef)
  //val bord: UintE =Wrapper.border[V,E,UI](dEv) //a déja calculé dev.
  /**  usefull both for lt, and for eq a single bit is on, iff operand on each edge side differ */
  val segmentOf1Apex: UintE = segment1(bordApex) //unop(orScan, bord)
  /** true if both values are different */
  val diffApex= elt(0,segmentOf1Apex)
  /** true if both values are equal */
  val eqApex= not(diffApex);
  val ltApex: BoolEf =Grad.ltApex(this,segmentOf1Apex)
  val gtApex=symEf(ltApex)
}
trait ComparApex2{
  self:UintV=>
  val ef: UintEf =apexEui(f(this))
  /** xor can be usefull for other things, so we keep a pointer to it */
  val bordApex: UintE =Wrapper.border[F,E,UI](ef)
  //val bord: UintE =Wrapper.border[V,E,UI](dEv) //a déja calculé dev.
  /**  usefull both for lt, and for eq a single bit is on, iff operand on each edge side differ */
  val segmentOf1Apex: UintE = segment1(bordApex) //unop(orScan, bord)
  /** true if both values are different */
  val diffApex= elt(0,segmentOf1Apex)
  val deriv:UintE=unop(derivative, segmentOf1Apex)
  val ltApex: BoolEf =Grad.ltApex2(ef,deriv,diffApex)
  val gtApex=symEf(ltApex)
}



/** add a boolVf lt3 which computes gt with respect to the two other neibors of the adjacent face, using an And transfer reduction redT*/
trait Compar3 {
  self: UintV with Compar =>
  val gt3:BoolVf=enlarge(transfer(gt))
}

/** add a functionnality to a boolVe: returns the symetric with respect to edge.  */
trait Sym extends BoolVe {
  val sym=neighborsSym(this)
}

/** permet de récupérer les voisin V, intUI */
trait SymUI extends UintVe {
  val symUI=neighborsSymUI(this)
}

/** contains addxxxx(arg) function which managas to add the functionality xxx to the argument arg */
object Util {
  /** return an unsigned vertex random integer of $n$ bits */
  def randUintV(nbits: Int): UintV = {//pb: quand nbits=1 ya un seul bit, ya pas de concat, et ca renvoie un boolV
    val tmp: Array[UintV] =Array.fill(nbits)(root4naming.addRandBit())
    tmp.reduce(_ :: _)  //all the random bits get concatenated.
  }

  /**
   *
   * @return first boolV is a randombit, which is true with proba 1/3 , but it may fail.
   *         second boolV indicates success
   */
  def oneThirdRandBit():(BoolV,BoolV)={
    val ri=randUintV(4)
    (ri<10,neq(ri))  //neq ri is true if ri is not null which happens with 7/8
  }
  /** return an unsigned vertex random integer of $n$ bits */
  def randConstUintV(nbits: Int): UintV = {//pb: quand nbits=1 ya un seul bit, ya pas de concat, et ca renvoie un boolV
    val tmp: Array[UintV] =Array.fill(nbits)(root4naming.addConstRandBit().asInstanceOf[UintV])
    tmp.reduce(_ :: _)  //all the random bits get concatenated.
  }

  /** we directly re use Delayed reaction, in order to be able to add  COmparison operators,
   * this naming will automatically define trucLt, trucEq, trucGt, trucLe, trucGe, mais sur les edges*/
  def addLt(_arg: => UintV): UintVx = {// with Compar with ComparApex with Compar3
    lazy val delayed = _arg;
    new AST.Delayed[(V, UI)](() => delayed) with ASTLt[V, UI] with Compar with ComparApex2  with Compar3 with Named with BranchNamed {}
  }
  def addLtSI(_arg: => SintV): SintVx = {// with Compar with ComparApex with Compar3
    lazy val delayed = _arg;
    new AST.Delayed[(V, SI)](() => delayed) with ASTLt[V, SI] with ComparSI with Named with BranchNamed {}
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
  def addBlobVe(_arg: => BoolVe,_toto: =>BoolE):BlobVe = {// with Compar with ComparApex with Compar3
    lazy val delayed = _arg;
    lazy val delayed2= _toto
    new AST.Delayed[(T[V,E], B)](() => delayed) with BoolVe with BlobVe with Named with BranchNamed {
       val brdVe: BoolVe = delayed
      val brdE=delayedL(delayed2) //grace a cet attribut, hasBrdE de blobVe est vérifié

    }
  }


  /** provide a boolVe with an additional fields sym */
  def addSym(_arg: => BoolVe) = {// with Compar with ComparApex with Compar3
    lazy val delayed = _arg;
    new AST.Delayed[(T[V,E], B)](() => delayed) with BoolVe with Sym with Named with BranchNamed {}
  }

  /** provide a boolVe with an additional fields sym */
  def addSymUI(_arg: => UintVe) = {// with Compar with ComparApex with Compar3
    lazy val delayed = _arg;
    new AST.Delayed[(T[V,E], UI)](() => delayed) with UintVe with SymUI with Named with BranchNamed {}
  }
  /**
   *
   * @param b represent a boolV offering computation of meeting points
   * @return places where growig will not cause merging of blobs.
   */
  def safeGrow(b:Blob):BoolV={
    val meetEside = existS[E, V](b.meetE) //true if adjacent to a meeting edge
    val meet = b.meetV | meetEside //  all meeting Vertices
    b.brdV //& ~meet
  }

}

/** Layer implementing a random bit */
class Rand() extends Layer[(V, B)](1, "random") with ASTLt[V, B]         {

  //val miroredNext = randNext(this) //by default it'll get mirored because of its radius 1.
  //val next: BoolV = torusify(miroredNext) //will apply the identity, plus torusify.
  val next: BoolV = randNext(torusify(this))//randDef is used only here, no need for a wrapper! torusify secures avoiding cycles in Rand
  lazy val randDir: BoolVe = {
    randN12(this)
  } //lazy because probably not used
  lazy val randSide: BoolEv = randE2(this) //only qpointRand uses this
}


