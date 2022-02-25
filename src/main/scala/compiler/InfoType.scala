package compiler

import Circuit.TabSymb
import VarKind.MacroField

/**
 * The most elementary info stored in symbol table: type and kind
 *
 * @param t spatial type of integer
 * @param k
 * @tparam T
 */
class InfoType[+T](val t: T, val k: VarKind) {
  override def toString: String = t.toString + " " + k.toString

  val repr1 = new repr(t)

  def locus: Locus = repr.lpart(repr1.asInstanceOf[repr[(_ <: Locus, _ <: Ring)]]).name

  def ring: Ring = repr.rpart(repr1.asInstanceOf[repr[(_ <: Locus, _ <: Ring)]]).name

  /** in some cases (i.e. creation of affectation, there is no obvious locus associated to the variable. */
  def locusOption: Option[Locus] = t match {
    case u@(_, _) => Some(u._1.asInstanceOf[Locus]) //if the type is a couple, the first is the locus
    case _ => None //if not,it's only a ring, because the locus could not be computed
  }

  /** when unfolding , some scalar have a locus, and some not */
  def ringSafe: Ring = t match {
    case u@(_, _) => u._2.asInstanceOf[Ring] //if the type is a locus, the first is the locus
    case _ => t.asInstanceOf[Ring]
  }
}

object InfoType {
  val sIntInfoNbit = new InfoNbit(SI(), MacroField(), 3)

  def apply(e: AST[_], k: VarKind): InfoType[_] = new InfoType(e.mym.name, k)

  def addSymb(t: TabSymb[InfoType[_]], e: AST[_], k: VarKind): t.type = t += e.name -> InfoType(e, k)

  def addSymbL(t: TabSymb[InfoType[_]], e: AST[_], k: VarKind): t.type = t += "l" + e.name -> InfoType(e, k)
}

object InfoNbit {

}
/**
 * info stored in symbol table, after computing nbit: type and kind and nbit
 *
 * @param t  type (locus+ring)
 * @param k  type of variable
 * @param nb number of bits.
 * @tparam T toto
 */
class InfoNbit[+T](override val t: T, override val k: VarKind, val nb: Int) extends InfoType(t, k) {
  def macroFieldise: InfoNbit[_] = new InfoNbit(t, MacroField(), nb)

  /** @return same info except we drop the locus and the type is ring   */
  def scalarify = this

  /*  : InfoNbit[Ring] = {
    new InfoNbit(ring, k, nb)
  }*/

  /**
   *
   * @param b
   * @return like scalarify, except that ifNeeded, it will generate a MacroField instead of ParamDfield, for redop;   */
  def regifyIf(b: Boolean) =
    new InfoNbit(t, if (!b) k else MacroField(), nb)

  val u = 2;

  override def toString: String = super.toString + " " + nb
}

/** information which will later allows to know wether we can pipeline through this class , when unfolding int */
case class Cost(nbTmpVar: Int, pipIn: Boolean, pipOut: Boolean)

class InfoPlusCost[+T](override val t: T, override val k: VarKind, override val nb: Int, val cost: Cost)
  extends InfoNbit(t, k, nb) {

}


/** OBSOLETE
 * add the possibility to represent an equivalence class.
 *
 * @param t  type (locus+ring)
 * @param k  type of variable
 * @param nb number of bits.
 * @tparam T toto
 */
class InfoCoalescedRegOld[+T](override val t: T, override val k: VarKind, override val nb: Int)
  extends InfoNbit(t, k, nb) with dataStruc.Union[InfoCoalescedRegOld[_]] {
  val v = 2;

  override def toString: String = super.toString + " " + nb
}

object InfoCoalescedRegOld {
  def apply(info: InfoNbit[_]): InfoCoalescedRegOld[_] = new InfoCoalescedRegOld(info.t, info.k, info.nb)

  //with dataStruc.Union[InfoCoalescedReg[_]]
}