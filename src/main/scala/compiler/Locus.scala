package compiler

import scala.collection.{Iterator, Seq}

/** The 9 locus. Three simplicial locus: V for vertex, E for edge, F for face, */
sealed abstract class Locus {
  /** @return where to print the variable of affect instructions, so that we can distinguish between S,E,F,T
   */
  def tabul: Int = this match {
    case V() => 0
    case E() => 3
    case F() => 5
    case T(_, _) => 9
  }


  def isTransfer = false

  /** how many bits are needed for a boolean field of this locus */
  def density: Int = if (isTransfer) 6 else sufx.length

  /** how many neighbors are adresed when doing a broadcast or the reverse, a reduce */
  def fanout = 6 / density

  /** suffix of variable names representing simplicial types.  arity is the locus's arity */
  val sufx: Array[String]

  /** generates allways 6 suffixe */
  def lessufx: Array[String]

  /** adds a suffix to a name in order to distinguish between the associated scalars encoding the spatial locus */

  def deploy(n: String): Array[String]

  /** encodes a neutral permutation with the right number of elements. */
  lazy val neutral: Array[Int] = Array.range(0, density) //we put lazy otherwise pb in initialization order
}

abstract class Modifier {
  def invert: Modifier
}

final case class Perimeter() extends Modifier {
  def invert = Radial()
}

final case class Radial() extends Modifier {
  def invert = Perimeter()
}

object Modifier {
  val invertModifier: Option[Modifier] => Option[Modifier] = {
    case Some(x) => Some(x.invert)
    case None => None
  }
}


abstract class S extends Locus with Ordered[S] {
  override def deploy(n: String): Array[String] = sufx.map(n + "$" + _)

  /** number of neighbor when doing a reduction */
  def propagateFrom(s: Array[Int], c: Array[Int]): Option[Array[Int]]

  def compare(that: S): Int = {
    toString.compareTo(that.toString)
  }

  /** defines which components are regrouped upon partitionning a transfer variable */
  val proj: Array[Int]

  /** @param t encodes a partitionnable transfer schedule on a son of this. vE or fE for E, vF or eF for F
   * @return the corresponding siplicial schedule on this */
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

  override def deploy(n: String) = Array(n)
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
  def lessufx: Array[String] = les6sufx
}

/** T stands for Transfer, and uses two simplicial locus. The first is the simplicial. T[V,E] corresponds to  eV  */
final case class T[+S1 <: S, +S2 <: S](from: S1, to: S2) extends TT {
  override def deploy(n: String) =
    from.sufx.map((suf1: String) => sufx.map(n + "$" + suf1 + _).toList).toList.flatten.toArray

  override def isTransfer = true

  def arity2 = from.density

  /** Suffix distinguishing   tlocus attached to the same slocus. for edge it is just a number, for face we distinguishes 3 angles;
   * for vertices there is 6 choices which do not have the same name for fV and eV */
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

  /**
   *
   * @param n name spatial field
   * @param l locus of n
   * @return list of name of corresponding scalar fields
   *         obtained by adding  one (resp. two) suffixes to n,
   */


  def deploy(n: String, l: Locus): List[String] = l match {
    case V() => List(n) //no need of dollars nor suffx we keep the same string
    case s: S => s.sufx.map(n + "$" + _).toList
    case T(s1, _) => s1.sufx.map((suf1: String) => l.sufx.map(n + "$" + suf1 + _).toList).toList.flatten
  }

}
