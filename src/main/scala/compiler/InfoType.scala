package compiler

import compiler.Circuit.TabSymb

/** The most elementary info stored in symbol table: type and kind */
class InfoType[+T](val t: T, val k: VarKind) {
  override def toString: String = t.toString + " " + k.toString
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
  val u = 2;

  override def toString: String = super.toString + " " + nb
}