package compiler
import AST.{Call1, _}
import ASTB.{Elt, _}
import compiler.ASTBfun.{Fundef2R, Fundef3R, negB, p}
import compiler.ASTLfun.halve
import compiler.SpatialType.BoolV
import ASTLfun._
import compiler.ASTBt.BB

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
  type Op2 = (BB, BB) => BB
  def p[R <: Ring](name: String)(implicit n: repr[R]) = new Param[R](name) with ASTBt[R]

  //---------------------------------------------Logical operation--------------------------//
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

  private val (negSI, negUI) = {
    def negI[R <: I](implicit m: repr[R]): Fundef1R[R] = {
      val xi = p[R]("xNegSi");
      Fundef1("negI", Mapp1(negB, List(xi)), xi)
    }

    (negI[SI], negI[UI])
  }
  def neg[R <: Ring](implicit n: repr[R]): Fundef1R[R] = (n.name match {
    case B() => negB
    case SI() => negSI
    case UI() => negUI
  }).asInstanceOf[Fundef1R[R]]

  /** for rapid production of orB,xorB, andB */
  def fundef2Bop2(op2: Op2, s: String): Fundef2[B, B, B] = {
    val (xb, yb) = (p[B]("x" + s), p[B]("y" + s));
    Fundef2("s", op2(xb, yb), xb, yb)
  }

  /** for rapid production of orI,xorI, andI I=SI/UI */
  def fundef2Imapp2[R <: I](op2: Fundef2R[B], s: String)(implicit m: repr[R]): Fundef2R[R] = {
    val (x, y) = (p[R]("x" + s), p[R]("y" + s));
    Fundef2("s", Mapp2(x, y, op2), x, y)
  }

  private val orB: Fundef2R[B] = fundef2Bop2(Or(_, _), "orb")
  private val (orSI, orUI) = {
    def orI[R <: I](implicit m: repr[R]) = fundef2Imapp2(orB, "orI"); (orI[SI], orI[UI])
  }
  def or[R <: Ring](implicit n: repr[R]): Fundef2R[R] = (n.name match {
    case B() => orB
    case SI() => orSI
    case UI() => orUI
  }).asInstanceOf[Fundef2R[R]]

  private val xorB: Fundef2R[B] = fundef2Bop2(Xor(_, _), "xorb")
  private val (xorSI, xorUI) = {
    def xorI[R <: I](implicit m: repr[R]) = fundef2Imapp2(xorB, "xorI"); (xorI[SI], xorI[UI])
  }

  def xor[R <: Ring](implicit n: repr[R]): Fundef2R[R] = (n.name match {
    case B() => xorB
    case SI() => xorSI
    case UI() => xorUI
  }).asInstanceOf[Fundef2R[R]]

  private val andB: Fundef2R[B] = fundef2Bop2(And(_, _), "andb")
  private val (andSI, andUI) = {
    def andI[R <: I](implicit m: repr[R]) = fundef2Imapp2(andB, "andI"); (andI[SI], andI[UI])
  }
  def and[R <: Ring](implicit n: repr[R]): Fundef2R[R] = (n.name match {
    case B() => andB
    case SI() => andSI
    case UI() => andUI
  }).asInstanceOf[Fundef2R[R]]

  /** applies a logical and of a boolean on all the integer, preserve the argument's type: SI or UI */

  private val (andLBtoRSI, andLBtoRUI) = {
    def andLBtoRI[R <: I]()(implicit n: repr[R]): Fundef2[B, R, R] = {
      val (xb, y) = (p[B]("xb"), p[R]("yandLBtoRI"))
      Fundef2("andLBtoR", Mapp1(
        {
          val yb = p[B]("yb");
          Fundef1("xb", xb & yb, yb)
        }, List(y, xb.asInstanceOf[ASTBt[R]], xb.asInstanceOf[ASTBt[R]])
      ), xb, y)
    }

    (andLBtoRI[SI], andLBtoRI[UI])
  }
  def andLBtoR[R <: Ring](implicit n: repr[R]): Fundef2R[R] = (n.name match {
    case SI() => andLBtoRSI
    case UI() => andLBtoRUI
    case B() => andB
  }).asInstanceOf[Fundef2R[R]]

  /** computes the classic carry used for summing 3 bits */
  val carry: Fundef3R[B] = {
    val (xb, yb, zb) = (p[B]("x"), p[B]("y"), p[B]("z"));
    Fundef3("carry", (xb & yb) | (zb & (xb | yb)), xb, yb, zb)
  }
  val uI2SI: Fundef1[UI, SI] = { //to be coherent with the other fundef declared as val, we call it uitosi insted uitosidef
    val xui = p[UI]("xuiToSi")
    Fundef1("uI2SI", Concat2(False(), xui), xui)
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

  //------------------------Arithmetic operation------------------------//

  /** could be done in a symetric way using xor, but takes more gates and more registers. */
  private val (addSI, addUI) = {
    def addI[R <: I](implicit n: repr[R]): Fundef2R[R] = {
      val (xsi, ysi) = (p[R]("xaddI"), p[R]("yaddI"));
      Fundef2("addI", Scan2(xsi, ysi, carry, False(), Left(), initUsed = true) ^ xsi ^ ysi, xsi, ysi)
    };
    (addI[SI], addI[UI])
  }
  def add[R <: Ring](implicit n: repr[R]): Fundef2R[R] = (n.name match {
    case SI() => addSI
    case UI() => addUI
  }).asInstanceOf[Fundef2R[R]]

  /** we will cast the argument to UI, when using it in ASTLfun, thus it will possible that ring gives boolean */
  val concat2UI = {
    val (x, y) = (p[UI]("xconcat2f"), p[UI]("yconcat2f"))
    Fundef2("concat2", Concat2[UI, UI, UI](x, y), x, y)
  }



  /** true if signed int parameter is stricty negative */
  //val lt1: Fundef1[SI, B] = { val x = p[SI]("x"); Fundef1("elt", Elt[SI](-1, x), x) }


  /** @param i final number of bits We generate a new funDef for each call, todo we should memoize this at least. */
  def extend[R <: Ring](i: Int)(implicit m: repr[R]): Fundef1[R, R] = {
    val x = p[R]("x");
    Fundef1("extend" + i + m.name,
      Extend[R](i, x), x)
  }


  def increaseRadius2[R <: Ring]()(implicit m: repr[R]): Fundef1[R, R] = { //todo faire un val au lieu d'un def
    val x: Param[R] with ASTBt[R] = p[R]("x");
    Fundef1("increaseRadius2",
      tm1(x), x) //will be decalified early, upon spatial unfolding, so that it can be removed at the detmize stage.
  }

  /** We generate a new funDef each time we want to read an element, todo we should memoize this at least. */

  def elt[R <: I](i: Int)(implicit n: repr[R]): Fundef1[R, B] = {
    val x = p[R]("xEltSi");
    Fundef1("elt" + i, Elt[R](i, x), x)
  }
  /** We generate a new funDef each time we want to read an element, todo we should memoize this at least. */

  private val (incSI, incUI) = {
    def incI[R <: I](implicit n: repr[R]): Fundef1R[R] = {
      val x = p[R]("xIncSi");
      Fundef1("inc", Scan1(x, andB, True(), Left(), initUsed = true) ^ x, x)
    };
    (incI[SI], incI[UI])
  }

  def inc[R <: Ring](implicit n: repr[R]): Fundef1[R, R] = (n.name match {
    case SI() => incSI
    case UI() => incUI
  }).asInstanceOf[Fundef1[R, R]]


  /** we cannot take the opp of a signe, fist convert it to an unsigned, which result in addint a zero */
  val oppSI: Fundef1R[SI] = {
    val x = p[SI]("xOppSi");
    Fundef1("opp",
      new Call1[SI, SI](incSI, (new Call1[SI, SI](negSI, x) with ASTBt[SI])) with ASTBt[SI], x)
  }

  //Comparison operation
  private val (neqSI, neqUI) = {
    def neqI[R <: I](implicit n: repr[R]): Fundef1[R, B] = {
      val x12 = p[R]("xneqSI");
      Fundef1("notNull", Reduce(x12, orB, False()), x12)
    }

    (neqI[SI], neqI[UI])
  }

  def neq[R <: Ring](implicit n: repr[R]): Fundef1[R, B] = (n.name match {
    case SI() => neqSI
    case UI() => neqUI
  }).asInstanceOf[Fundef1[R, B]]


  private val (eqSI, eqUI) = {
    def eqI[R <: I](implicit n: repr[R]): Fundef1[R, B] = {
      val x12 = p[R]("xneqSI");
      Fundef1("notNull", ~Reduce(x12, orB, False()), x12)
    };
    (eqI[SI], eqI[UI])
  }
  /** return true if integer is  zero */
  def eq[R <: I](implicit n: repr[R]) = (n.name match {
    case SI() => eqSI
    case UI() => eqUI
  }).asInstanceOf[Fundef1[R, B]]

  /** true if signed integer is strictly negative */
  val ltSI: Fundef1[SI, B] = elt[SI](-1)

  /*

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
    /** comparing two signed int is done by testing the sign of the difference*/
    val leSI2: Fundef2[SI, SI, B] = {
      val (x, y) = (p[SI]("xleSI2"), p[SI]("yleSI2"));
      Fundef2("leSI2", (new Call1[SI, B](leSI1, x - y) with ASTBt[B]), x, y)
    }
  */


  /**
   * This sign is the 2 bit unsigned int corresponding to -1 (11) 0 (00) and 1 (01) ready to be extended and added
   * when concating in ASTBfun, we directly use Concat2, with apropirate type */
  val sign: Fundef1R[SI] = {
    val x = p[SI]("xsign");
    Fundef1("sign", Concat2[B, B, SI](new Call1[SI, B](neqSI, x) with ASTBt[B], Elt(-1, x)), x)
  } //TODO remplacer 2 par size.

  /** return the minimum of two signs, which is easier to compute than the minimum of two 2 bits integers, due to the fact that only three values are possible */
  val minSign: Fundef2R[SI] = {
    val (xsi, ysi) = (p[SI]("xminSign"), p[SI]("yminSign"))
    Fundef2("minSign", {
      val bitsign: Bool = Elt(1, xsi) | Elt(1, ysi)
      val bit0: Bool = bitsign | ((~bitsign) & //si le bit de signe est négatif ca doit etre 11
        //sinon pour que le bit 0 soit 1, il faut que les deux bit O soit 1. car le min est soit zero soit 1
        ((Elt(0, xsi) & Elt(0, ysi)))
        )
      Concat2[B, B, SI](bit0, bitsign) //we concat the two bits
    },
      xsi, ysi)
  }
  private val condB: Fundef3R[B] = {
    val (bbool, tthen, eelse) = (p[B]("bbool"), p[B]("tthen"), p[B]("eelse"))
    Fundef3("cond", bbool & (tthen) | (~bbool).&(eelse), bbool, tthen, eelse)
  }
  private val (condSI, condUI) = {
    def condI[R <: I]()(implicit n: repr[R]): Fundef3[B, R, R, R] = {
      val (bbool, tthen, eelse) = (p[B]("bbool"), p[R]("tthen"), p[R]("eelse"))
      Fundef3("cond", (bbool.&(tthen)(n) | (~bbool).&(eelse)(n)).asInstanceOf[ASTBt[R]], bbool, tthen, eelse)
    }

    (condI[SI], condI[UI])
  }

  def cond[R <: Ring](implicit n: repr[R]): Fundef2R[R] = (n.name match {
    case B() => condB
    case SI() => condSI
    case UI() => condUI
  }).asInstanceOf[Fundef2R[R]]


  /** used together with scan */


  private val (halveBSI, halveBUI) = {
  val other: Fundef2R[B] = {
    val (xb, yb) = (p[B]("xb"), p[B]("yb"));
    Fundef2("other", yb, xb, yb)
  }

    def halveBI[R <: I](implicit n: repr[R]): Fundef1R[R] = {
      val x = p[R]("xhalveB");
    Fundef1("halve", Scan1(x, other, False(), Right(), initUsed = true), x)
    };
    (halveBI[SI], halveBI[UI])
  }

  /** result in shifting bits towards the tail, entering a zero at the end of the list,
   * it would divide by two an unsigned integers */
  def halveB[R <: I](implicit n: repr[R]) = (n.name match {
    case SI() => halveBSI
    case UI() => halveBUI
  }).asInstanceOf[Fundef1[R, R]]


  private val (orScanRightSI, orScanRightUI) = {
    def orScanRightI[R <: I](implicit n: repr[R]): Fundef1R[R] = {
      val x = p[R]("orScanRightB");
      Fundef1("orScanRight", Scan1(x, orB, False(), Right(), initUsed = false), x)
    };
    (orScanRightI[SI], orScanRightI[UI])
  }

  def orScanRight[R <: I](implicit n: repr[R]) = (n.name match {
    case SI() => orScanRightSI
    case UI() => orScanRightUI
  }).asInstanceOf[Fundef1[R, R]]

  /** optimal implementation of comparison between two unsigned integers, using orscanright like operators, */
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
      null
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