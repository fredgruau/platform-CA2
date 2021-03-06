package compiler
import scala.collection.{Iterator, Seq}

/**The 9 locus. Three simplicial locus: V for vertex, E for edge, F for face, */
sealed abstract class Locus {
  /**suffix of variable names representing simplicial types */
  val sufx: Array[String]
  /** arity is the locus's arity */
  def lessufx: Array[String]
  def isTransfer = false
  def density: Int = if (isTransfer) 6 else sufx.length

  /**encodes a neutral permutation with the right number of elements. */
  lazy val neutral: Array[Int] = Array.range(0, density) //we put lazy otherwise pb in initialization order
}
abstract class S extends Locus with Ordered[S] {

  /** number of neighbor when doing a reduction */
  def fanout=6/density
  def propagateFrom(s: Array[Int], c: Array[Int]): Option[Array[Int]]
  def compare(that: S): Int = { toString.compareTo(that.toString) }
  /** defines which components are regrouped upon partitionning a transfer variable */
  val proj: Array[Int]
  /**@param t encodes a partitionnable transfer schedule on a son of this. vE or fE for E, vF or eF for F
   * @return the corresponding siplicial schedule on this*/
  def scheduleProj(t:Seq[Int]):Array[Int]
  /**Number of distinct transfer schedules that can be partitionned with a given simplicial schedule*/
  val card: Int

  /**Number of schedule that can be partitionned and verify a strict ordering */
  val cardSucc: Int
  def partitionnables: Option[Iterator[Array[Int]]]
  /**@param a encodes a  schedule on a transfer locus which  son of this. vE or fE for E, vF or eF for F
  @return true if this scheduled can be partitionned */
  def partitionable(a:scala.Seq[Int]):Boolean
  def lessufx=sufx

}
final case class V() extends S {
  val sufx  = Array("")
  val proj: Array[Int] = Array(0, 0, 0, 0, 0, 0); val card = 0; val cardSucc = 0
  def propagateFrom(s: Array[Int], c: Array[Int]): Option[Array[Int]] = None
  /** how to project a schedule, useless for V */
  override def scheduleProj(t: Seq[Int]): Array[Int] = Array(0)
  def partitionnables: Option[  Iterator[Array[Int]]] =  None
  def partitionable(a:scala.Seq[Int])=true
}

final case class E() extends S {
  /* "h" stands for horizontal, "d" diagonal, "ad" antidiagonal */
  val sufx  = Array("h", "d", "ad")
  val proj: Array[Int] = Array(0, 0, 1, 1, 2, 2); val card = 48; val cardSucc = 6
  def propagateFrom(s: Array[Int], c: Array[Int]): Option[Array[Int]] = Some(Array(c(s(0) * 2), c(s(0) * 2) + 1, c(s(1) * 2), c(s(1) * 2) + 1, c(s(2) * 2), c(s(2) * 2) + 1))
  /** how to project a schedule */
 // override def scheduleProj(t: Seq[Int]): Array[Int] = Array(proj(t.head),proj(t(2)),proj(t(4)))
  override def scheduleProj(t: Seq[Int]): Array[Int] = Array(t(0),t(2), t(4) )
  private val modif=List(Array(0,0,0),Array(0,0,1),Array(0,1,0),Array(0,1,1),Array(1,0,0),Array(1,0,1),Array(1,1,0),Array(1,1,1) )
  private def combine(t:Array[Int],u:Array[Int]): Array[Int] =Array(t(0)+u(0),t(0)+1- u(0),t(1)+u(1),t(1)+1- u(1),t(2)+u(2),t(2)+1-u(2))
  def partitionnables: Option[Iterator[Array[Int]]] = Some(Array(0, 2, 4).permutations.flatMap((t: Array[Int]) => modif.map(combine(t, _))))
  def partitionable(a:scala.Seq[Int])=a(0)==a(1)&&a(2)==a(3)&&a(4)==a(5)
}

final case class F() extends S {
  val sufx  = Array("up", "do"); val proj: Array[Int] = Array(0, 0, 0, 1, 1, 1); val card = 48; val cardSucc = 2
  def propagateFrom(s: Array[Int], c: Array[Int]): Option[Array[Int]] = Some(Array(c(s(0) * 3), c(s(0) * 3) + 1, c(s(0) * 3 + 2), c(s(1) * 3), c(s(1) * 3) + 1, c(s(1) * 3 + 2)))
  override def scheduleProj(t: Seq[Int]): Array[Int] = Array( t(0),t(3))
  private val  p2=List(3,4,5).permutations
  private def combine(t:List[Int],u:List[Int]): Seq[Array[ Int]] = List( (t:::u).toArray,(u:::t).toArray )
  def partitionnables: Option[Iterator[Array[Int]]] = Some( List(0, 1, 2).permutations.flatMap((t: List[Int]) => p2.map(combine(t, _))).flatten)
  def partitionable(a:scala.Seq[Int])=a(0)==a(1)&&a(1)==a(2)&&a(3)==a(4)&& a(4)==a(5)
}

abstract class TT extends Locus{
  def arity2:Int
  def les6sufx: Array[String]
  def lessufx=les6sufx
}

/** T stands for Transfer, and uses two simplicial locus. The first is the simplicial. T[V,E] corresponds to  eV  */
final case class T[+S1 <: S, +S2 <: S](from: S1, to: S2) extends TT {
  override def isTransfer = true
  def arity2=from.density
  /** Suffix distinguishing   tlocus attached to the same slocus. for edge it is just a number, for face we distinguishes 3 angles;
   * for vertices there is 6 choices which do not have the same name for fV and eV*/
  val sufx: Array[String] = from match {
    case V() => to match {
      case E() => Array("w", "nw", "ne", "e", "se", "sw")
      case F() => Array("wn", "n", "en", "es", "s", "ws")
    }
    case E() => to match {
      case V() | F() => Array("1", "2")
    }
    case F() => to match {
      case V() => Array("p", "b1", "b2")
      case E() => Array("b", "s1", "s2")
    } //"s" stands for side, "b" for base.
  }

  // lazy val les6sufx: Array[String]  = from.sufx.flatMap  ((suf1: String) => to.sufx.map((suf2: String) =>  suf1+suf2  ))
  /** return all the names of the locus.  */
  lazy val les6sufx: Array[String]  = from match {   case V() => sufx
  case _ => from.sufx.flatMap  ((suf1: String) => sufx.map((suf2: String) =>  suf1+suf2  ))}

}
object Locus {

  /**add one (resp. two) suffixes to the variable names, for simplicial (resp. tranfer) variable */

  def deploy(n: String, l: Locus): List[String] = l match {
    case s: S      => s.sufx.map(n + "$" + _).toList
    case T(s1, _) => s1.sufx.map((suf1: String) => l.sufx.map(n + "$" + suf1 + _).toList).toList.flatten
  }

}
