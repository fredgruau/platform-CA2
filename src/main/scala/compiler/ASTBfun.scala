package compiler
import AST.{Call1, _}
import ASTB.{Elt, _}
import compiler.ASTBfun.{negB, p}
import compiler.ASTLfun.halve
import compiler.SpatialType.BoolV
import ASTLfun._

/** Contains the code of logical function defined as val, to avoid reproducting the code several times, when they are used in BINOP or UNOP
 * todo function which use bool Constructors should be moved to ASTB, so that we can declare those constructors, private.
 * ACHTUNGACHTUNGACHTUNGACHTUNG BECAUSE FUNCTIONS ARE HERE DEFINED AS VAL, IT IS IMPORTANT THAT
 * THEY SHOULD BE DECLARED IN THE RIGHT ORDER OTHERWISE IT WILL RESULT IN TROUBLESOME NUL VALUES
 * THAT I TAKE A LONG TIME TO SPOT */
object ASTBfun {
  type ASTBg = ASTBt[_ <: Ring]
  type Fundef3R[R <: Ring] = Fundef3[R, R, R, R]
  type Fundef2R[R <: Ring] = Fundef2[R, R, R]
  type Fundef1R[R <: Ring] = Fundef1[R, R]

  def p[R <: Ring](name: String)(implicit n: repr[R]) = new Param[R](name) with ASTBt[R]

  /*
    /** Used for debug */
    val identityB: Fundef1R[B] = {
      val xb = p[B]("xIdentityB");
      Fundef1("identityB", xb, xb)
    }
    /** Used for debug */
    val identitySI: Fundef1R[SI] = {
      val xi = p[SI]("xidentitySI");
      Fundef1("identitySI", Mapp1(identityB, List(xi)), xi)
    }
    /** Used for debug */
    val identityUI: Fundef1R[UI] = {
      val xi = p[UI]("xidentityUI");
      Fundef1("identityUI", Mapp1(identityB, List(xi)), xi)
    }*/
  val negB: Fundef1R[B] = {
    val xb = p[B]("xNegB");
    Fundef1("negB", Neg(xb), xb)
  }

  private def negI[R <: I](implicit m: repr[R]): Fundef1R[R] = {
    val xi = p[R]("xNegSi");
    Fundef1("negI", Mapp1(negB, List(xi)), xi)
  }

  private val (negSI, negUI) = (negI[SI], negI[UI])

  def neg[R <: Ring](implicit n: repr[R]): Fundef1R[R] = (n.name match {
    case B() => negB
    case SI() => negSI
    case UI() => negUI

  }).asInstanceOf[Fundef1R[R]]


  private val orB: Fundef2R[B] = {
    val (xb, yb) = (p[B]("xb"), p[B]("yb"));
    Fundef2("orB", Or(xb, yb), xb, yb)
  }

  private def orI[R <: I](implicit m: repr[R]): Fundef2R[R] = {
    val (x, y) = (p[R]("OrI"), p[R]("yOrSi"));
    Fundef2("orI", Mapp2(x, y, orB), x, y)
  };
  private val (orSI, orUI) = (orI[SI], orI[UI])

  def or[R <: Ring](implicit n: repr[R]): Fundef2R[R] = (n.name match {
    case B() => orB
    case SI() => orSI
    case UI() => orUI
  }).asInstanceOf[Fundef2R[R]]


  private val andB: Fundef2R[B] = {
    val (xb, yb) = (p[B]("xb"), p[B]("yb"));
    Fundef2("andB", And(xb, yb), xb, yb)
  }

  private def andI[R <: I](implicit m: repr[R]): Fundef2R[R] = {
    val (x, y) = (p[R]("xAndSi"), p[R]("yAndSi"));
    Fundef2("andI", Mapp2(x, y, andB), x, y)
  };
  private val (andSI, andUI) = (andI[SI], andI[UI])

  def and[R <: Ring](implicit n: repr[R]): Fundef2R[R] = (n.name match {
    case B() => andB
    case SI() => andSI
    case UI() => andUI
  }).asInstanceOf[Fundef2R[R]]

  private val xorB: Fundef2R[B] = {
    val (xb, yb) = (p[B]("xb"), p[B]("yb"));
    Fundef2("xorB", Xor(xb, yb), xb, yb)
  }

  private def xorI[R <: I](implicit m: repr[R]): Fundef2R[R] = {
    val (x, y) = (p[R]("x"), p[R]("y"));
    Fundef2("xorI", Mapp2(x, y, xorB), x, y)
  };
  private val (xorSI, xorUI) = (xorI[SI], xorI[UI])

  def xor[R <: Ring](implicit n: repr[R]): Fundef2R[R] = (n.name match {
    case B() => xorB
    case SI() => xorSI
    case UI() => xorUI
  }).asInstanceOf[Fundef2R[R]]

  /** applies a logical and of a boolean on all the integer, preserve the argument's type: SI or UI */
  private def andLBtoRI[R <: I]()(implicit n: repr[R]): Fundef2[B, R, R] = {
    val (xb, y) = (p[B]("xb"), p[R]("yandLBtoRI"))
    Fundef2("andLBtoR", Mapp1(
      {
        val yb = p[B]("yb");
        Fundef1("xb", xb & yb, yb)
      }, List(y, xb.asInstanceOf[ASTBt[R]], xb.asInstanceOf[ASTBt[R]])
    ), xb, y)
  }

  private val (andLBtoRSI, andLBtoRUI) = (andLBtoRI[SI], andLBtoRI[UI])

  def andLBtoR[R <: Ring](implicit n: repr[R]): Fundef2R[R] = (n.name match {
    case SI() => andLBtoRSI
    case UI() => andLBtoRUI
  }).asInstanceOf[Fundef2R[R]]

  /** computes the classic carry used for summing 3 bits */
  val carry: Fundef3R[B] = {
    val (xb, yb, zb) = (p[B]("x"), p[B]("y"), p[B]("z"));
    Fundef3("carry", (xb & yb) | (zb & (xb | yb)), xb, yb, zb)
  }
  /*
   sub is implemented in MyAST BoolOP
    val subSI: Fundef2R[SI] = {
      val (xsi, ysi) = (p[SI]("xSubSi"), p[SI]("ySubSi"));
      Fundef2("subSI", ysi - xsi, xsi, ysi) //renvoie sur opp qui lui est défini
    } //could be done in a symetric way using xor, but takes more gates and more registers.

  */
  val uI2SI: Fundef1[UI, SI] = { //to be coherent with the other fundef declared as val, we call it uitosi insted uitosidef
    val xui = p[UI]("xuiToSi")
    Fundef1("uI2SI", Concat2(False(), xui), xui) //renvoie sur opp qui lui est défini
  }
  /*
    /** wrapper */
    def uItoSIcall(xui: Uint): Sint = new Call1[UI, SI](uItoSI, xui) with Sint

    /** unsigned int argument needs to be extended with one bit, in order to represent now, signed int */
    val subUI: Fundef2[UI, UI, SI] = {
      val (xsi, ysi) = (p[UI]("xsubUI"), p[UI]("ysubUI"));
      Fundef2("subSI", uItoSIcall(ysi) - uItoSIcall(xsi), xsi, ysi) //renvoie sur opp qui lui est défini

    } //could be done in a symetric way using xor, but takes more gates and more registers.

    val ltUI2: Fundef2[UI, UI, B] = {
      val (x, y) = (p[UI]("x"), p[UI]("y"));
      Fundef2[UI, UI, B]("ltUI2", (new Call1[UI, B](ltSI1, uItoSI(x) - uItoSI(y)) with ASTBt[B]), x, y)
    }
  */

  /** could be done in a symetric way using xor, but takes more gates and more registers. */
  private def addI[R <: I](implicit n: repr[R]): Fundef2R[R] = {
    val (xsi, ysi) = (p[R]("xaddI"), p[R]("yaddI"));
    Fundef2("addI", Scan2(xsi, ysi, carry, False(), Left(), initUsed = true) ^ xsi ^ ysi, xsi, ysi)
  };
  private val addSI = addI[SI];
  private val addUI = addI[UI]

  def add[R <: Ring](implicit n: repr[R]): Fundef2R[R] = (n.name match {
    case SI() => addSI
    case UI() => addUI
  }).asInstanceOf[Fundef2R[R]]
  /*
val addSI: Fundef2R[SI] = {
  val (xsi, ysi) = (p[SI]("xAddSi"), p[SI]("yAddSi"));
  Fundef2("addSI", Scan2(xsi, ysi, carry, False(), Left(), initUsed = true) ^ xsi ^ ysi, xsi, ysi)
}

  def addUISI(r: Ring) = r match {
    case SI() => addSI
    case UI() => addUIandSI
    case _ => throw new Exception("decide between signed or unsigned integer")
  }
*/


  def concat2I[R <: I](implicit n: repr[R]): Fundef2[B, I, I] = {
    val (x, y) = (p[B]("xconcat2f"), p[R]("yconcat2f"))
    Fundef2("concat2I", Concat2(x, y), x, y)
  }

  private val concat2SI = concat2I[SI];
  private val concat2UI = concat2I[UI]

  def concat2[R <: Ring](implicit n: repr[R]) = n.name match {
    case SI() => concat2SI
    case UI() => concat2UI
  }

  /** true if signed int parameter is stricty negative */
  //val lt1: Fundef1[SI, B] = { val x = p[SI]("x"); Fundef1("elt", Elt[SI](-1, x), x) }


  /** @param i final number of bits */
  def extend[R <: Ring](i: Int)(implicit m: repr[R]): Fundef1[R, R] = {
    val x = p[R]("x");
    Fundef1("extend" + i + m.name,
      Extend[R](i, x), x)
  }

  /*  def increaseRadius[R <: Ring]()(implicit m: repr[R]): Fundef1[R, R] = {
      val x = p[R]("x");
      Fundef1("increaseRadius",
        IncreaseRadius[R](x), x)
    }*/

  def increaseRadius2[R <: Ring]()(implicit m: repr[R]): Fundef1[R, R] = { //todo faire un val au lieu d'un def
    val x: Param[R] with ASTBt[R] = p[R]("x");
    Fundef1("increaseRadius2",
      tm1(x), x) //will be decalified early, upon spatial unfolding, so that it can be removed at the detmize stage.
  }

  /** @param i final number of bits, We generate a new funDef for each call, todo we should memoize this at least. */
  def extendSI(i: Int): Fundef1[SI, SI] = {
    val x = p[SI]("x");
    Fundef1("extend" + i, Extend[SI](i, x), x)
  }

  /** We generate a new funDef each time we want to read an element, todo we should memoize this at least. */
  def eltSI(i: Int): Fundef1[SI, B] = {
    val x = p[SI]("xEltSi");
    Fundef1("elt" + i, Elt[SI](i, x), x)
  }

  /** We generate a new funDef each time we want to read an element, todo we should memoize this at least. */
  def eltUI(i: Int): Fundef1[UI, B] = {
    val x = p[UI]("xEltUi");
    Fundef1("elt" + i, Elt[UI](i, x), x)
  }

  def eltUISI(r: Ring, i: Int) = r match {
    case SI() => eltSI(i)
    case UI() => eltUI(i)
    case _ => throw new Exception("decide between signed or unsigned integer")
  }


  // addition must be programmed
  val incSI: Fundef1R[SI] = {
    val x = p[SI]("xIncSi");
    Fundef1("inc",
      Scan1(x, andB, True(), Left(), initUsed = true) ^ x, x)
  } //TODO a tester


  // addition must be programmed
  val incUI: Fundef1R[UI] = {
    val x = p[UI]("xIncUi");
    Fundef1("inc", Scan1(x, andB, True(), Left(), initUsed = true) ^ x, x)
  } //TODO a tester


  //todo Attention, si on prends le opp d'un unsigned, faudra vérifier que ca devient un signed, et que la taille augmente. (commencer par concateter 0)
  val oppSI: Fundef1R[SI] = {
    val x = p[SI]("xOppSi");
    Fundef1("opp",
      new Call1[SI, SI](incSI, (new Call1[SI, SI](negSI.asInstanceOf[Fundef1R[SI]], x) with ASTBt[SI])) with ASTBt[SI], x)
    //new Call1(negSI.asInstanceOf[Fundef1R[SI]], x) with ASTBt[SI], x)
  }


  //Comparison operation

  val neqSI: Fundef1[SI, B] = {
    val x12 = p[SI]("xneqSI");
    Fundef1("notNull", Reduce(x12, orB, False()), x12)
  }


  val neqUI: Fundef1[UI, B] = {
    val x12 = p[UI]("xneqUI");
    Fundef1("notNull", Reduce(x12, orB, False()), x12)
  }


  /** return true if integer is  zero */
  val eqSI: Fundef1[SI, B] = {
    val x12 = p[SI]("xeqSI");
    val noteq: Bool = new Call1[SI, B](neqSI, x12) with ASTBt[B]
    //val neq:Bool= ~(new Call1[SI,B](neqSI, x12)(repr.nomB) with ASTBt[B])
    val eq: Bool = ~noteq
    Fundef1[SI, B]("isZero", eq, x12)
  }


  /** true if signed integer is strictly negative */
  val ltSI: Fundef1[SI, B] = eltSI(-1).asInstanceOf[Fundef1[SI, B]]

  /** true if first argument strictly smaller than second with respect to the modulo order */
  val ltSI2Mod: Fundef2[SI, SI, B] = {
    val (x, y) = (p[SI]("xLtSi"), p[SI]("yxLtSi"));
    Fundef2("ltSI2", (new Call1[SI, B](ltSI, x - y) with ASTBt[B]), x, y) //ltsi1(z) true if z strictly negative
  }
  /** true if first argument strictly greater than second */
  val gtSI2: Fundef2[SI, SI, B] = {
    val (x, y) = (p[SI]("xgtSI2"), p[SI]("ygtSI2"));
    Fundef2("gtSI2", (new Call1[SI, B](ltSI, y - x) with ASTBt[B]), x, y)
  }

  /** true if integer is  negative or null */
  val leSI1: Fundef1[SI, B] = {
    val x18 = p[SI]("xleSI1");
    Fundef1("leSI1",
      new Call1[SI, B](ltSI, x18) with ASTBt[B] | new Call1[SI, B](eqSI, x18) with ASTBt[B], x18)
  }

  val leSI2: Fundef2[SI, SI, B] = {
    val (x, y) = (p[SI]("xleSI2"), p[SI]("yleSI2"));
    Fundef2("leSI2", (new Call1[SI, B](leSI1, x - y) with ASTBt[B]), x, y)
  }


  /**
   * This sign is the 2 bit unsigned int corresponding to -1 (11) 0 (00) and 1 (01) ready to be extended and added   */
  val sign: Fundef1R[SI] = {
    val x = p[SI]("xsign");
    Fundef1("sign", Concat2(new Call1[SI, B](neqSI, x) with ASTBt[B], Elt(-1, x)), x)
  } //TODO remplacer 2 par size.


  val minSign: Fundef2R[SI] = {
    val (xsi, ysi) = (p[SI]("xminSign"), p[SI]("yminSign"))
    Fundef2("minSign", {
      val bitsign: Bool = Elt(1, xsi) | Elt(1, ysi)
      val bit0: Bool = bitsign | ((~bitsign) & //si le bit de signe est négatif ca doit etre 11
        //sinon pour que le bit 0 soit 1, il faut que les deux bit O soit 1. car le min est soit zero soit 1
        ((Elt(0, xsi) & Elt(0, ysi)))
        )
      Concat2(bit0, bitsign)(new repr(SI()))
    },
      xsi, ysi)
  }



  /*

    val andLBtoRSI: Fundef2[B, SI, SI] = {
      val (xb, y) = (p[B]("xb"), p[SI]("yandLBtoRSI"))
      Fundef2("andLBtoR", Mapp1(
        {  val yb = p[B]("yb"); Fundef1("xb", xb & yb, yb)
        }, List(y, xb.asInstanceOf[ASTBt[SI]], xb.asInstanceOf[ASTBt[SI]])
      ), xb, y)
    }
    /** applies a logical and of a boolean on all the integer */
    val andLBtoRUI: Fundef2[B, UI, UI] = {
      val (xb, y) = (p[B]("xb"), p[UI]("yandLBtoRUI"))
      Fundef2("andLBtoR", Mapp1(
        {  val yb = p[B]("yb"); Fundef1("xb", xb & yb, yb)
        }, List(y, xb.asInstanceOf[ASTBt[UI]], xb.asInstanceOf[ASTBt[UI]])
      ), xb, y)
    }
  */


  /* def andLBtoRUISI(r: Ring) = r match {
     case SI() =>
       andLBtoRSI
     case UI() =>
       andLBtoRUI
     case _ => throw new Exception("decide between signed or unsigned integer")
   }
 */

  /** */
  val condSI: Fundef3[B, SI, SI, SI] = {
    val (bbool, tthen, eelse) = (p[B]("bbool"), p[SI]("tthen"), p[SI]("eelse"))
    Fundef3("cond", bbool.&(tthen)(repr.nomSI).asInstanceOf[ASTBt[SI]] |
      (~bbool).&(eelse)(repr.nomSI).asInstanceOf[ASTBt[SI]],
      bbool, tthen, eelse)
  }
  val condUI: Fundef3[B, UI, UI, UI] = {
    val (bbool, tthen, eelse) = (p[B]("bbool"), p[UI]("tthen"), p[UI]("eelse"))
    Fundef3("cond", bbool.&(tthen)(repr.nomUI).asInstanceOf[ASTBt[UI]] |
      (~bbool).&(eelse)(repr.nomUI).asInstanceOf[ASTBt[UI]],
      bbool, tthen, eelse)
  }


  val minRelSI: Fundef2R[SI] = {
    val (xsi, ysi) = (p[SI]("xminSI"), p[SI]("yminSI"));
    Fundef2("minSI", new Call3[B, SI, SI, SI](condSI, (new Call2[SI, SI, B](ltSI2Mod, xsi, ysi) with ASTBt[B]), xsi, ysi) with ASTBt[SI],
      xsi, ysi).asInstanceOf[Fundef2R[SI]]
  }

  val other: Fundef2R[B] = {
    val (xb, yb) = (p[B]("xb"), p[B]("yb"));
    Fundef2("other", yb, xb, yb)
  }

  /** result in shifting bits towards the tail, entering a zero at the end of the list,
   * it would divide by two is SI was to be UI */
  val halveBSI: Fundef1R[SI] = {
    val x = p[SI]("xhalveB");
    Fundef1("halve", Scan1(x, other, False(), Right(), initUsed = true), x)
  } //TODO dire que c'est halveUI

  val halveBUI: Fundef1R[UI] = {
    val x = p[UI]("xhalveB");
    Fundef1("halve", Scan1(x, other, False(), Right(), initUsed = true), x)
  } //TODO dire que c'est halveUI

  def orScanRightB[R <: I](implicit n: repr[R]): Fundef1R[R] = {
    val x = p[R]("orScanRightB");
    Fundef1("orScanRight", Scan1(x, orB, False(), Right(), initUsed = false), x)
  }

  val orScanRightUI = orScanRightB[UI]

  /** optimal implementation of comparison between two unsigned integers */
  val ltUI2: Fundef2[UI, UI, B] = {
    val (xui, yui) = (p[UI]("xminUI"), p[UI]("yminUI"));
    val difference = xui ^ yui //true for bits which differs betwen xui and yui
    val segmentOf1: Uint = Scan1(difference, orB, False(), Right(), initUsed = false) //fills with one, starting from the rightmost 1 to the first leftmost least significant bit
    //we have to affect segmentof1 because it is read simultaneously at two indexes, for first1.
    val first1: Uint = ~(new Call1[UI, UI](halveBUI, segmentOf1) with ASTBt[UI]) & segmentOf1 //only the rightmost msb bits remains. halveBui must comes first otherwise it bugs
    // true if yui was the one with most significant bit of difference set to 1, that is a strict lower than
    Fundef2("ltUI", new Call1[UI, B](neqUI, first1 & yui) with ASTBt[B], xui, yui) //todo ecrire des xor et des and pour les ui
  } //TODO a faire correct en utilisant ltUI.


  val minUI: Fundef2R[UI] = {
    val (xsi, ysi) = (p[UI]("xminUI"), p[UI]("yminUI"));
    Fundef2("minUI", new Call3[B, UI, UI, UI](condUI, (new Call2[UI, UI, B](ltUI2, xsi, ysi) with ASTBt[B]), xsi, ysi) with ASTBt[UI],
      xsi, ysi).asInstanceOf[Fundef2R[UI]]
  }
  /*
 /** does a reduction from SintVe to SintV, not including the center. Used for distancve  */
 val reduceMinRelSI[S1 <: S, S2 <: S](arg: ASTLt[T[S1,S2], SI])
  (implicit m: repr[S1], n: repr[S2], d: chipBorder[S2, S1]): ASTLt[S2, SI] = {
   val f: Fundef1[(S1, SI), (S2, SI)] = getRedSFun(minRedop[SI], arg.locus)(m, n, repr.nomSI, d)
   new Call1[(S1, SI), (S2, SI)](f, arg)(repr.nomLR(n, compiler.repr.nomSI)) with ASTLt[S2, SI] {}
 }*/

  // def notNull[R <: I](x: ASTB[R]) = FoldLeft1(x, Or[B])

  //(orI.asInstanceOf[Fundef2[R, R, R]], False[R]
  /** a reduction operator is a function taking two arguement of the same type R, and returning a result also of type R. plus a neutral value */
  type redop[R <: Ring] = (Fundef2R[R], ASTBt[R])

  /** *
   * todo finish
   * @return
   */
  def concatRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
    if (n.name.isInstanceOf[SI]) (orSI.asInstanceOf[Fundef2[R, R, R]], Intof[SI](-1).asInstanceOf[ASTB[R]])
    if (n.name.isInstanceOf[UI]) (orUI.asInstanceOf[Fundef2[R, R, R]], Intof[SI](-1).asInstanceOf[ASTB[R]])
    else (orB.asInstanceOf[Fundef2[R, R, R]], False().asInstanceOf[ASTB[R]])
  }

  def orRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
    if (n.name.isInstanceOf[SI]) (orSI.asInstanceOf[Fundef2[R, R, R]], Intof[SI](-1).asInstanceOf[ASTB[R]])
    else if (n.name.isInstanceOf[UI]) (orUI.asInstanceOf[Fundef2[R, R, R]], Intof[UI](-1).asInstanceOf[ASTB[R]])
    else (orB.asInstanceOf[Fundef2[R, R, R]], False().asInstanceOf[ASTB[R]])
  }

  def andRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
    if (n.name.isInstanceOf[SI]) (andSI.asInstanceOf[Fundef2[R, R, R]], Intof[SI](0).asInstanceOf[ASTB[R]])
    if (n.name.isInstanceOf[UI]) (andUI.asInstanceOf[Fundef2[R, R, R]], Intof[SI](0).asInstanceOf[ASTB[R]])
    else (andB.asInstanceOf[Fundef2[R, R, R]], False().asInstanceOf[ASTB[R]])
  }

  def xorRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
    if (n.name.isInstanceOf[SI]) (xorSI.asInstanceOf[Fundef2[R, R, R]], Intof[SI](0).asInstanceOf[ASTB[R]])
    if (n.name.isInstanceOf[UI]) (xorUI.asInstanceOf[Fundef2[R, R, R]], Intof[UI](0).asInstanceOf[ASTB[R]])
    else (xorB.asInstanceOf[Fundef2[R, R, R]], False().asInstanceOf[ASTB[R]])
  }

  /** min on signed integers is relative, min on unsigned integer is absolute */
  def minRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
    /** returns the biggest signed constant on n bits, where n is adjusted at run time, when the constant is combined
     * to some other integer, using a binop. The bitifying stage   is able to extends, adding  the correct  number of bits
     */
    def maxSI = (new Call1[SI, SI](halveBSI, ASTB.Intof[SI](-1)(repr.nomSI)) with ASTBt[SI])
    if (n.name.isInstanceOf[UI])
      (minUI.asInstanceOf[Fundef2[R, R, R]],
        ~(ASTB.Intof[UI](0)(repr.nomUI)).asInstanceOf[ASTBt[R]])
    else if (n.name.isInstanceOf[SI]) {
      assert(false, "not defined yet, this is a relative minimum")
      (minRelSI.asInstanceOf[Fundef2[R, R, R]], maxSI.asInstanceOf[ASTBt[R]] //todo check if that is ok
      )
    }
    else {
      assert(false, "not SI nor UI, min is not defined on booleans");
      null
    }
  }


  /** 1 is the greatest value for sign, which can only be -1, 0, 1 */
  val minSignRedop: redop[SI] = (minSign, Intof[SI](1))
  //todo definir un addRedop,
  val addRedopSI: redop[SI] = (addSI, Intof[SI](0))
  val addRedopUI: redop[UI] = (addUI, Intof[UI](0))

  def addRedop[R <: Ring](implicit n: repr[R]) = n.name match {
    case SI() => addRedopSI
    case UI() => addRedopUI
  }

}