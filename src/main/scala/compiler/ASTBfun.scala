package compiler

import compiler.AST._
import compiler.ASTB._
 /** Contains the code of logical function */
object ASTBfun {
   type ASTB1[R <: Ring] = ASTBt[R]
  type ASTBg = ASTBt[_ <: Ring]
  type Fundef3R[R <: Ring] = Fundef3[R, R, R, R]
  type Fundef2R[R <: Ring] = Fundef2[R, R, R]
  type Fundef1R[R <: Ring] = Fundef1[R, R]


  private def p[R <: Ring](name: String)(implicit n: repr[R]) = new Param[R](name) with ASTBt[R]

   val negB: Fundef1R[B] = {
     val xb = p[B]("xb"); Fundef1("negB", Neg(xb), xb)
   }
   val negI: Fundef1R[UISI] = {
     val xi = p[UISI]("xi"); Fundef1("negI", Mapp1(xi, negB), xi)
   }
   val orB: Fundef2R[B] = {
     val (xb, yb) = (p[B]("xb"), p[B]("yb")); Fundef2("orB", Or(xb, yb), xb, yb)
   }
   val orI: Fundef2R[UISI] = {
     val (x, y) = (p[UISI]("x"), p[UISI]("y")); Fundef2("orI", Mapp2(x, y, orB), x, y)
   }
   val andB: Fundef2R[B] = {
     val (xb, yb) = (p[B]("xb"), p[B]("yb")); Fundef2("andB", And(xb, yb), xb, yb)
   }
   val andI: Fundef2R[UISI] = {
     val (x, y) = (p[UISI]("x"), p[UISI]("y")); Fundef2("andI", Mapp2(x, y, andB), x, y)
   }
   val xorB: Fundef2R[B] = {
     val (xb, yb) = (p[B]("xb"), p[B]("yb")); Fundef2("xorB", Xor(xb, yb), xb, yb)
   }
   val xorI: Fundef2R[UISI] = {
     val (x, y) = (p[UISI]("x"), p[UISI]("y")); Fundef2("xorI", Mapp2(x, y, xorB), x, y)
   }
   val carry: Fundef3R[B] = {
     val (xb, yb, zb) = (p[B]("x"), p[B]("y"), p[B]("z")); Fundef3("carry", (xb & yb) | (zb & (xb | yb)), xb, yb, zb)
   }
   val minSI: Fundef2R[SI] = {
     val (xsi, ysi) = (p[SI]("xsi"), p[SI]("ysi")); Fundef2("minSI", Mapp2(xsi, ysi, xorB), xsi, ysi)
   } //TODO a faire correct en utilisant gt.
   val subSI: Fundef2R[SI] = {
     val (xsi, ysi) = (p[SI]("xsi"), p[SI]("ysi")); Fundef2("subSI", ysi - xsi, xsi, ysi)
   } //could be done in a symetric way using xor, but takes more gates and more registers.
   val addSI: Fundef2R[SI] = {
     val (xsi, ysi) = (p[SI]("xsi"), p[SI]("ysi")); Fundef2("addSI", ysi - xsi, xsi, ysi)
   } //could be done in a symetric way using xor, but takes more gates and more registers.
   val minUI: Fundef2R[UI] = {
     val (xui, yui) = (p[UI]("xui"), p[UI]("yui")); Fundef2("minUI", Mapp2(xui, yui, xorB), xui, yui)
   } //TODO a faire correct en utilisant .

   //(orI.asInstanceOf[Fundef2[R, R, R]], False[R]
   type redop[R <: Ring] = (Fundef2R[R], ASTBt[R])

   def orRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
     if (n.name.isInstanceOf[I]) (orI.asInstanceOf[Fundef2[R, R, R]], Intof[UISI](-1).asInstanceOf[ASTB[R]])
     else (orB.asInstanceOf[Fundef2[R, R, R]], Boolof(false).asInstanceOf[ASTB[R]])
   }

   def andRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
     if (n.name.isInstanceOf[I]) (andI.asInstanceOf[Fundef2[R, R, R]], Intof[UISI](-1).asInstanceOf[ASTB[R]])
     else (andB.asInstanceOf[Fundef2[R, R, R]], Boolof(false).asInstanceOf[ASTB[R]])
   }

   def xorRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
     if (n.name.isInstanceOf[I]) (xorI.asInstanceOf[Fundef2[R, R, R]], Intof[UISI](0).asInstanceOf[ASTB[R]])
     else (xorB.asInstanceOf[Fundef2[R, R, R]], Boolof(false).asInstanceOf[ASTB[R]])
   }
  
  val andLBtoR: Fundef2[B, UISI, UISI] = { val (xb, y) = (p[B]("xb"), p[UISI]("y"))
    Fundef2( "andLBtoR", Mapp1(y, {val yb = p[B]("yb");  Fundef1("toto",xb & yb,yb )}    ), xb, y) }
 val concat2f: Fundef2[UISIB,UISIB,UISI] = { val (x, y) = (p[UISIB]("x"), p[UISIB]("y"))
   Fundef2( "concat",  Concat2(x,y), x , y) }
  def elt(i: Int): Fundef1[UISI, B] = { val x = p[UISI]("x"); Fundef1("elt", Elt[UISI](i, x), x) }
  def extend(i: Int): Fundef1[UISI, UISI] = { val x = p[UISI]("x"); Fundef1("extend" + i, Extend[UISI](i, x), x) }
  // addition must be programmed
  val inc: Fundef1R[UISI] = { val x = p[UISI]("x"); Fundef1("inc", x ^ Scan1(x, andB, true, Left(), initUsed = true), x) } //TODO a tester
  //val gtB: Fundef1[SI,B] = { val xsi = Param[SI]("xsi"); Fundef1("gt",   Concat2( Elt(2), x) } //TODO a tester
//  val addI: Fundef2R[UISI] = { val (x, y) = (p[UISI]("x"), p[UISI]("y")); Fundef2("add", x ^ y ^ Scan2(x, y, carry, False[B], Left(), true), x, y) }
//  def add2[R <: I](implicit n: repr[R]) = { val (x, y) = (p[R]("x"), p[R]("y")); Fundef2("add", x ^ y ^ Scan2(x, y, carry, False[B], Left(), true), x, y) }
  val addUISI: Fundef2[UISI, UISI, UISI] = { val (x, y) = (p[UISI]("x"), p[UISI]("y")); Fundef2("add", x ^ y ^ Scan2(x, y, carry, false, Left(), initUsed = true), x, y) }
 
  // def addI[R <: I](implicit n: repr[R]): Fundef2R[R] = addUISI.asInstanceOf[Fundef2R[R]] 

  val notNullB: Fundef1[UISI, B] = { val x12 = p[UISI]("x"); Fundef1("notNull", Reduce(x12, orB, false), x12) }
  val sign: Fundef1R[SI] = { val x = p[SI]("x"); Fundef1("sign", Concat2(new Call1(notNullB, x) with ASTBt[B], Elt(-1, x)), x) } //TODO remplacer 2 par size.

  //Attention, lorsq'on prend le opp d'un unsigned, faut vérifier que ca devient un signe, et que la taille augmente. (commencer par concateter 0)
  val oppSI: Fundef1R[SI] = { val x = p[SI]("x");   Fundef1("opp", new Call1(inc.asInstanceOf[Fundef1R[SI]], Neg(x).asInstanceOf[AST[SI]]) with ASTBt[SI], x) }
  val other: Fundef2R[B] = { val (xb, yb) = (p[B]("xb"), p[B]("yb")); Fundef2("other", yb, xb, yb) }
  /** result in shifting bits towards the tail, entering a zero at the end of the list  */
  val halveB: Fundef1R[UISI] = { val x = p[UISI]("x"); Fundef1("halve", Scan1(x, other, false, Right(), initUsed = true), x) } //TODO a tester
  val orScanRightB: Fundef1R[UISI] = { val x = p[UISI]("x"); Fundef1("orScanRight", Scan1(x, orB, false, Right(), initUsed = false), x) }
  // def notNull[R <: I](x: ASTB[R]) = FoldLeft1(x, Or[B])

}