package compiler

import AST.{Call1, _}
import ASTB.{Elt, _}

/** Contains the code of logical function
 * ACHTUNGACHTUNGACHTUNGACHTUNG FUNCTIONS ARE HERE DEFINED AS VAL, IT IS IMPORTANT THAT
 * THEY SHOULD BE DECLARED IN THE RIGHT ORDER OTHERWISE IT WILL RESULT IN TROUBLESOME NUL VALUES
 * THAT I TAKE A LONG TIME TO SPOT */
object ASTBfun {
  type ASTB1[R <: Ring] = ASTBt[R]
  type ASTBg = ASTBt[_ <: Ring]
  type Fundef3R[R <: Ring] = Fundef3[R, R, R, R]
  type Fundef2R[R <: Ring] = Fundef2[R, R, R]
  type Fundef1R[R <: Ring] = Fundef1[R, R]


  private def p[R <: Ring](name: String)(implicit n: repr[R]) = new Param[R](name) with ASTBt[R]

  val negB: Fundef1R[B] = {
    val xb = p[B]("xb");
    Fundef1("negB", Neg(xb), xb)
  }
  val negSI: Fundef1R[SI] = {
    val xi = p[SI]("xi");
    Fundef1("negI", Mapp1(negB, List(xi)), xi)
  }
  val orB: Fundef2R[B] = {
    val (xb, yb) = (p[B]("xb"), p[B]("yb"));
    Fundef2("orB", Or(xb, yb), xb, yb)
  }
  val orSI: Fundef2R[SI] = {
    val (x, y) = (p[SI]("x"), p[SI]("y"));
    Fundef2("orI", Mapp2(x, y, orB), x, y)
  }
  val orUI: Fundef2R[UI] = {
    val (x, y) = (p[UI]("x"), p[UI]("y"));
    Fundef2("orI", Mapp2(x, y, orB), x, y)
  }

  def orUISI(r: Ring) = r match {
    case SI() => orSI
    case UI() => orUI
    case _ => throw new Exception("decide between signed or unsigned integer")
  }

  val andB: Fundef2R[B] = {
    val (xb, yb) = (p[B]("xb"), p[B]("yb"));
    Fundef2("andB", And(xb, yb), xb, yb)
  }

  //  val andI: Fundef2R[UISI] = {
  //    val (x, y) = (p[UISI]("x"), p[UISI]("y"));
  //    Fundef2("andI", Mapp2(x, y, andB), x, y)
  //  }

  val andSI: Fundef2R[SI] = {
    val (x, y) = (p[SI]("x"), p[SI]("y"));
    Fundef2("andI", Mapp2(x, y, andB), x, y)
  }
  val andUI: Fundef2R[UI] = {
    val (x, y) = (p[UI]("x"), p[UI]("y"));
    Fundef2("andI", Mapp2(x, y, andB), x, y)
  }

  def andUISI(r: Ring) = r match {
    case SI() => andSI
    case UI() => andUI
    case _ => throw new Exception("decide between signed or unsigned integer")
  }

  val xorB: Fundef2R[B] = {
    val (xb, yb) = (p[B]("xb"), p[B]("yb"));
    Fundef2("xorB", Xor(xb, yb), xb, yb)
  }
  //  val xorI: Fundef2R[UISI] = {
  //    val (x, y) = (p[UISI]("x"), p[UISI]("y"));
  //    Fundef2("xorI", Mapp2(x, y, xorB), x, y)
  //  }
  val xorSI: Fundef2R[SI] = {
    val (x, y) = (p[SI]("x"), p[SI]("y"));
    Fundef2("xorI", Mapp2(x, y, xorB), x, y)
  }
  val xorUI: Fundef2R[UI] = {
    val (x, y) = (p[UI]("x"), p[UI]("y"));
    Fundef2("xorI", Mapp2(x, y, xorB), x, y)
  }

  def xorUISI(r: Ring) = r match {
    case SI() => xorSI
    case UI() => xorUI
    case _ => throw new Exception("decide between signed or unsigned integer")
  }

  val carry: Fundef3R[B] = {
    val (xb, yb, zb) = (p[B]("x"), p[B]("y"), p[B]("z"));
    Fundef3("carry", (xb & yb) | (zb & (xb | yb)), xb, yb, zb)
  }

  val subSI: Fundef2R[SI] = {
    val (xsi, ysi) = (p[SI]("xsi"), p[SI]("ysi"));
    Fundef2("subSI", ysi - xsi, xsi, ysi) //renvoie sur opp qui lui est défini

  } //could be done in a symetric way using xor, but takes more gates and more registers.


  //addSI is using addUISI, it must be declared after otherwise the op will "null", we had several time this null op syndrom
  val addSI: Fundef2R[SI] = {
    val (xsi, ysi) = (p[SI]("xsi"), p[SI]("ysi"));
    Fundef2("addSI", Scan2(xsi, ysi, carry, False(), Left(), initUsed = true) ^ xsi ^ ysi, xsi, ysi)
  } //could be done in a symetric way using xor, but takes more gates and more registers.

  val addUI: Fundef2R[UI] = {
    val (xsi, ysi) = (p[UI]("xsi"), p[UI]("ysi"));
    Fundef2("addSI", Scan2(xsi, ysi, carry, False(), Left(), initUsed = true) ^ xsi ^ ysi, xsi, ysi)
  } //could be done in a symetric way using xor, but takes more gates and more registers.

  def addUISI(r: Ring) = r match {
    case SI() => addSI
    case UI() => addUI
    case _ => throw new Exception("decide between signed or unsigned integer")
  }

  val concat2f: Fundef2[UISIB, UISIB, UISI] = {
    val (x, y) = (p[UISIB]("x"), p[UISIB]("y"))
    Fundef2("concat", Concat2(x, y), x, y)
  }
  /** true if signed int parameter is stricty negative */
  //val lt1: Fundef1[SI, B] = { val x = p[SI]("x"); Fundef1("elt", Elt[SI](-1, x), x) }


  /** @param i final number of bits */
  def extend[R <: Ring](i: Int)(implicit m: repr[R]): Fundef1[R, R] = {
    val x = p[R]("x");
    Fundef1("extend" + i + m.name,
      Extend[R](i, x), x)
  }

  /** @param i final number of bits */
  def extendSI(i: Int): Fundef1[SI, SI] = {
    val x = p[SI]("x");
    Fundef1("extend" + i, Extend[SI](i, x), x)
  }


  def eltSI(i: Int): Fundef1[SI, B] = {
    val x = p[SI]("x");
    Fundef1("elt" + i, Elt[SI](i, x), x)
  }

  def eltUI(i: Int): Fundef1[UI, B] = {
    val x = p[UI]("x");
    Fundef1("elt" + i, Elt[UI](i, x), x)
  }

  def eltUISI(r: Ring, i: Int) = r match {
    case SI() => eltSI(i)
    case UI() => eltUI(i)
    case _ => throw new Exception("decide between signed or unsigned integer")
  }


  // addition must be programmed
  val incSI: Fundef1R[SI] = {
    val x = p[SI]("x");
    Fundef1("inc", Scan1(x, andB, True(), Left(), initUsed = true) ^ x, x)
  } //TODO a tester


  // addition must be programmed
  val incUI: Fundef1R[UI] = {
    val x = p[UI]("x");
    Fundef1("inc", Scan1(x, andB, True(), Left(), initUsed = true) ^ x, x)
  } //TODO a tester


  //Attention, lorsq'on prend le opp d'un unsigned, faut vérifier que ca devient un signe, et que la taille augmente. (commencer par concateter 0)
  val oppSI: Fundef1R[SI] = {
    val x = p[SI]("x");
    Fundef1("opp",
      // new Call1(inc.asInstanceOf[Fundef1R[SI]], Neg(x).asInstanceOf[AST[SI]]) with ASTBt[SI], x) }
      new Call1(incSI,
        (new Call1(negSI.asInstanceOf[Fundef1R[SI]], x) with ASTBt[SI]).asInstanceOf[AST[SI]]) with ASTBt[SI], x)
  }


  //Comparison operation

  val neqSI: Fundef1[SI, B] = {
    val x12 = p[SI]("x");
    Fundef1("notNull", Reduce(x12, orB, False()), x12)
  }

  val neqUI: Fundef1[UI, B] = {
    val x12 = p[UI]("x");
    Fundef1("notNull", Reduce(x12, orB, False()), x12)
  }

  /** return true if integer is  null */
  val eqSI: Fundef1[SI, B] = {
    val x12 = p[SI]("x");
    Fundef1("notNull", ~new Call1(neqSI, x12) with ASTBt[B], x12)
  }

  /** true if integer is strictly negative */
  val ltSI1: Fundef1[SI, B] = eltSI(-1).asInstanceOf[Fundef1[SI, B]]

  /** true if first argument strictly smaller than second */
  val ltSI2: Fundef2[SI, SI, B] = {
    val (x, y) = (p[SI]("x"), p[SI]("y"));
    Fundef2("ltSI2", (new Call1(ltSI1, x - y) with ASTBt[B]), x, y)
  }
  /** true if integer is  negative or null */
  val leSI1: Fundef1[SI, B] = {
    val x18 = p[SI]("x");
    Fundef1("leSI1",
      new Call1(ltSI1, x18) with ASTBt[B] | new Call1(eqSI, x18) with ASTBt[B], x18)
  }

  val leSI2: Fundef2[SI, SI, B] = {
    val (x, y) = (p[SI]("x"), p[SI]("y"));
    Fundef2("leSI2", (new Call1(leSI1, x - y) with ASTBt[B]), x, y)
  }


  /**
   * This sign is the 2 bit unsigned int corresponding to -1 (11) 0 (00) and 1 (01) ready to be extended and added   */
  val sign: Fundef1R[SI] = {
    val x = p[SI]("x");
    Fundef1("sign", Concat2(new Call1(neqSI, x) with ASTBt[B], Elt(-1, x)), x)
  } //TODO remplacer 2 par size.


  val minSign: Fundef2R[SI] = {
    val (xsi, ysi) = (p[SI]("xui"), p[SI]("yui"))
    Fundef2("minSign", {
      val bitsign: ASTBt[B] = Elt(1, xsi) | Elt(1, ysi)
      val bit0: ASTBt[B] = bitsign | ((~bitsign) &
        ((Elt(0, xsi) | Elt(0, ysi)))
        )
      Concat2(bit0, bitsign)(new repr(SI()))
    },
      xsi, ysi)
  }

  /** applies a logical and of a boolean on all the integer */
  val andLBtoRSI: Fundef2[B, SI, SI] = {
    val (xb, y) = (p[B]("xb"), p[SI]("y"))
    Fundef2("andLBtoR", Mapp1(
      {
        val yb = p[B]("yb"); Fundef1("xb", xb & yb, yb)
      }, List(y, xb.asInstanceOf[ASTBt[SI]], xb.asInstanceOf[ASTBt[SI]])
    ), xb, y)
  }
  /** applies a logical and of a boolean on all the integer */
  val andLBtoRUI: Fundef2[B, UI, UI] = {
    val (xb, y) = (p[B]("xb"), p[UI]("y"))
    Fundef2("andLBtoR", Mapp1(
      {
        val yb = p[B]("yb"); Fundef1("xb", xb & yb, yb)
      }, List(y, xb.asInstanceOf[ASTBt[UI]], xb.asInstanceOf[ASTBt[UI]])
    ), xb, y)
  }


  def andLBtoRUISI(r: Ring) = r match {
    case SI() => andLBtoRSI
    case UI() => andLBtoRUI
    case _ => throw new Exception("decide between signed or unsigned integer")
  }


  /** */
  val condSI: Fundef3[B, SI, SI, SI] = {
    val (bbool, tthen, eelse) = (p[B]("bbool"), p[SI]("tthen"), p[SI]("eelse"))
    Fundef3("cond", bbool.&(tthen)(repr.nomSI).asInstanceOf[ASTBt[SI]] |
      (~bbool).&(eelse)(repr.nomSI).asInstanceOf[ASTBt[SI]],
      bbool, tthen, eelse)
  }


  val minSI: Fundef2R[SI] = {
    val (xsi, ysi) = (p[SI]("xui"), p[SI]("yui"));
    Fundef2("minSI", new Call3(condSI, (new Call2(ltSI2, xsi, ysi) with ASTBt[B]), xsi, ysi) with ASTBt[SI],
      xsi, ysi).asInstanceOf[Fundef2R[SI]]
  }

  val minUI: Fundef2R[UI] = {
    val (xui, yui) = (p[UI]("xui"), p[UI]("yui"));
    Fundef2("minUI", Mapp2(xui, yui, xorB), xui, yui)
  } //TODO a faire correct en utilisant ltUI.

  val other: Fundef2R[B] = {
    val (xb, yb) = (p[B]("xb"), p[B]("yb"));
    Fundef2("other", yb, xb, yb)
  }

  /** result in shifting bits towards the tail, entering a zero at the end of the list  */
  val halveB: Fundef1R[UISI] = {
    val x = p[UISI]("x");
    Fundef1("halve", Scan1(x, other, False(), Right(), initUsed = true), x)
  } //TODO a tester
  val orScanRightB: Fundef1R[UISI] = {
    val x = p[UISI]("x");
    Fundef1("orScanRight", Scan1(x, orB, False(), Right(), initUsed = false), x)
  }
  // def notNull[R <: I](x: ASTB[R]) = FoldLeft1(x, Or[B])

  //(orI.asInstanceOf[Fundef2[R, R, R]], False[R]
  type redop[R <: Ring] = (Fundef2R[R], ASTBt[R])

  def orRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
    if (n.name.isInstanceOf[SI]) (orSI.asInstanceOf[Fundef2[R, R, R]], Intof[SI](-1).asInstanceOf[ASTB[R]])
    else if (n.name.isInstanceOf[UI]) (orUI.asInstanceOf[Fundef2[R, R, R]], Intof[UI](-1).asInstanceOf[ASTB[R]])
    else (orB.asInstanceOf[Fundef2[R, R, R]], False().asInstanceOf[ASTB[R]])

  }

  def andRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
    if (n.name.isInstanceOf[SI]) (andSI.asInstanceOf[Fundef2[R, R, R]], Intof[SI](0).asInstanceOf[ASTB[R]])
    else if (n.name.isInstanceOf[UI]) (andUI.asInstanceOf[Fundef2[R, R, R]], Intof[UI](0).asInstanceOf[ASTB[R]])
    else (andB.asInstanceOf[Fundef2[R, R, R]], False().asInstanceOf[ASTB[R]])
  }

  def xorRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
    if (n.name.isInstanceOf[SI]) (xorSI.asInstanceOf[Fundef2[R, R, R]], Intof[SI](0).asInstanceOf[ASTB[R]])
    else if (n.name.isInstanceOf[UI]) (xorUI.asInstanceOf[Fundef2[R, R, R]], Intof[UI](0).asInstanceOf[ASTB[R]])
    else (xorB.asInstanceOf[Fundef2[R, R, R]], False().asInstanceOf[ASTB[R]])
  }
}