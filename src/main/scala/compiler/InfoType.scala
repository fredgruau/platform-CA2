package compiler

import compiler.Circuit.TabSymb
import compiler.VarKind.MacroField

/** The most elementary info stored in symbol table: type and kind */
class InfoType[+T](val t: T, val k: VarKind) {
  override def toString: String = t.toString + " " + k.toString

  val repr1 = new repr(t)

  def locus: Locus = repr.lpart(repr1.asInstanceOf[repr[(_ <: compiler.Locus, _ <: compiler.Ring)]]).name

  def ring: Ring = repr.rpart(repr1.asInstanceOf[repr[(_ <: compiler.Locus, _ <: compiler.Ring)]]).name

}

object InfoType {
  def apply(e: AST[_], k: VarKind): InfoType[_] = new InfoType(e.mym.name, k)

  def addSymb(t: TabSymb[InfoType[_]], e: AST[_], k: VarKind): t.type = t += e.name -> InfoType(e, k)

  def addSymbL(t: TabSymb[InfoType[_]], e: AST[_], k: VarKind): t.type = t += "l" + e.name -> InfoType(e, k)
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
  /**
   *
   * @return same info except we drop the locus and the type is ring
   */
  def scalarify: InfoNbit[Ring] = {
    new InfoNbit(ring, k, nb)
  }

  /**
   *
   * @param b
   * @return like scalarify, except that ifNeeded, it will generate a MacroField instead of ParamDfield, for redop;   */
  def regifyIf(b: Boolean): InfoNbit[Ring] =
    new InfoNbit(ring, if (!b) k else MacroField(), nb)

  val u = 2;

  override def toString: String = super.toString + " " + nb
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