package compiler

import AST.{Call1, Fundef2, _}
import ASTB.{Elt, Scan1, _}
import compiler.ASTBfun.{Fundef1R, Fundef2R, Fundef3R, fundef2Bop2, halfSIsurUI, negB, p, redop}
import compiler.ASTLfun.halve
import compiler.SpatialType.BoolV
import ASTLfun._
import compiler.ASTBt.BB
import compiler.MyOpB

/** Contains the code of logical function defined as val, to avoid reproducting the code several times, when they are used in BINOP or UNOP
 * todo function which use bool Constructors should be moved to ASTB, so that we can declare those constructors, private.
 * ACHTUNGACHTUNGACHTUNGACHTUNG BECAUSE FUNCTIONS ARE HERE DEFINED AS VAL, IT IS IMPORTANT THAT
 * THEY SHOULD BE DECLARED IN THE RIGHT ORDER OTHERWISE IT WILL RESULT IN TROUBLESOME NUL VALUES
 * THAT I TAKE A LONG TIME TO SPOT */
object ASTBfun {
  type ASTBg = ASTBt[_ <: Ring]
  type Fundef3R[R <: Ring] = Fundef3[R, R, R, R]
  type Fundef2R[R <: Ring] = Fundef2[R, R, R]

  type Fundef2RB[R <: Ring] = Fundef2[R, R, B]
  type Fundef2RP[R <: Ring,P<:Ring] = Fundef2[R, R, P]
  type Fundef1R[R <: Ring] = Fundef1[R, R]
  type Op2 = (BB, BB) => BB
  def p[R <: Ring](name: String)(implicit n: repr[R]) = new Param[R](name) with ASTBt[R]

  //---------------------------------------------Logical operation--------------------------//
  /** for rapid production of orB,xorB, andB */
  def fundef2Bop2(op2: Op2, s: String): Fundef2[B, B, B] = {
    val (xb, yb) = (p[B]("x" + s), p[B]("y" + s));
    Fundef2(s, op2(xb, yb), xb, yb)
  }

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
    }

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


  /** used with cac */
  val delta: Fundef2R[B] = {
    val (xb, yb) = (p[B]("deltax"), p[B]("deltay"));
    Fundef2("delta", xb & ~yb, xb, yb)
  }
  val deltaInv: Fundef2R[B] = {
    val (xb, yb) = (p[B]("deltax"), p[B]("deltay"));
    Fundef2("delta", yb & ~xb, xb, yb)
  }
  val andB: Fundef2R[B] = fundef2Bop2(And(_, _), "andb")
  private val (andSI, andUI) = {
    def andI[R <: I](implicit m: repr[R]) = fundef2Imapp2(andB, "andI"); (andI[SI], andI[UI])
  }
  def and[R <: Ring](implicit n: repr[R]): Fundef2R[R] = (n.name match {
    case B() => andB
    case SI() => andSI
    case UI() => andUI
  }).asInstanceOf[Fundef2R[R]]
  /** for rapid production of orI,xorI, andI I=SI/UI */
  def fundef2Imapp2[R <: I](op2: Fundef2R[B], s: String)(implicit m: repr[R]): Fundef2R[R] = {
    val (x, y) = (p[R]("x" + s), p[R]("y" + s));
    Fundef2(s, Mapp2(x, y, op2), x, y)
  }

  val orB: Fundef2R[B] = fundef2Bop2(Or(_, _), "orb")
  private val (orSI, orUI) = {
    def orI[R <: I](implicit m: repr[R]) = fundef2Imapp2(orB, "orI"); (orI[SI], orI[UI])
  }


  val concatB: Fundef2[B, UI, UI] = {
    val (xb, yui) = (p[B]("xb"), p[UI]("yui"))
    Fundef2("concat2", Concat2(xb, yui), xb, yui)
  }

  val concatUI: Fundef2[UI, UI, UI] = {
    val (xui, yui) = (p[UI]("xui"), p[UI]("yui"))
    Fundef2("concaat2", Concat2(xui, yui), xui, yui)
  }


  /*
    val concat2BUI: Fundef2R[UI]= fundef2Bop2(
      (Concat2(_:ASTBt[_], _:ASTBt[_])(repr.nomUI))
      .asInstanceOf[Op2], "concat2")
      .asInstanceOf[Fundef2R[UI]]*/
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
    Fundef1("uI2SI", Concat2( xui,False()), xui)
  }  /** the rand layers used to build an integer are stored in a hashMap, so as to be found by the naming algo */
  val b2SI: Fundef1[B,SI] = {
    val xb = p[B]("xBtoSi")
    Fundef1("b2SI", Concat2(xb,False()), xb)
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
  val allOneUI: Fundef1[UI,B]= {
      val x13 = p[UI]("xallOneUI");
      Fundef1("allOneUI", Reduce(x13, andB, False()), x13)
  }

  //Comparison operation
  private val (neqSI, neqUI) = {
    def neqI[R <: I](implicit n: repr[R]): Fundef1[R, B] = {
      val x12 = p[R]("xneqSI");
      Fundef1("notFalse", Reduce(x12, orB, False()), x12)
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
  def eq[R <: Ring](implicit n: repr[R]) = (n.name match {
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

  val isneg: Fundef1[SI,B]={
    val x = p[SI]("xxsign");
    Fundef1("isneg",  Elt(-1, x), x)
  }

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

  val other: Fundef2R[B] = {
    val (xb, yb) = (p[B]("xb"), p[B]("yb"));
    Fundef2("other", yb, xb, yb)
  }

  /** does as if the argument was a signed integer, when halving. This means that the last bit which is the sign, is preserved */
  val halfSIsurUI={
    val xh = p[UI]("xh");
    val last=Elt(-1,xh)
    Fundef1("halfSIsurUI", Scan1(xh, other, last, Right(), initUsed = true), xh)
  };

  private val (halveBSI, halveBUI) = {


    def halveBI[R <: I](implicit n: repr[R]): Fundef1R[R] = {
      val x = p[R]("xhalveB");
      Fundef1("halve", Scan1(x, other, False(), Right(), initUsed = true), x)
    };
    (halveBI[SI], halveBI[UI])
  }

  /*private val (dropMsbSI, dropMsbUI) = {
    val other2: Fundef2R[B] = {
      val (xb, yb) = (p[B]("xb"), p[B]("yb"));
      Fundef2("other2", xb, xb, yb)
    }

    def dropMsb[R <: I](implicit n: repr[R]): Fundef1R[R] = {
      val x = p[R]("xdropB");
      Fundef1("dropMsb", Scan1(x, other2, False(), Right(), initUsed = true), x)
    };
    (dropMsb[SI], dropMsb[UI])
  }
*/

  /** result in shifting bits towards the tail, entering a zero at the end of the list,
   * it would divide by two an unsigned integers. The bit size does not change*/
  def halveB[R <: I](implicit n: repr[R]) = (n.name match {
    case SI() => halveBSI
    case UI() => halveBUI
  }).asInstanceOf[Fundef1[R, R]]


  /** the call to halve remove the LSB elt(0) which reappers as the first bit after the concatenation, thus rotating the bits to the right */
  val rotUI = {
    val x = p[UI]("xrot");
    Fundef1[UI, UI]("rot", (new Call1[UI, UI](halveBUI, x)(repr.nomUI)
      with ASTBt[UI]) ::
      (new Call1[UI, B](elt(0), x)(repr.nomB)
        with ASTBt[B]).asInstanceOf[ASTBt[UI]], x)
  }


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

  /** non equality between two unsigned integers, */
  val eqUI2: Fundef2[UI, UI, B] = {
    val (xui, yui) = (p[UI]("xminUI"), p[UI]("yminUI")); //a t-on x < y
    val difference = xui ^ yui //true for bits which differs betwen xui and yu
    Fundef2("neqUI", new Call1[UI, B](neqUI, difference) with ASTBt[B], xui, yui) //todo ecrire des xor et des and pour les ui
  } //TODO a faire correct en utilisant ltUI.



  /** non equality between two unsigned integers, */
  val neqUI2: Fundef2[UI, UI, B] = {
    val (xui, yui) = (p[UI]("xminUI"), p[UI]("yminUI")); //a t-on x < y
    val difference = xui ^ yui //true for bits which differs betwen xui and yu
    Fundef2("neqUI", new Call1[UI, B](neqUI, difference) with ASTBt[B], xui, yui) //todo ecrire des xor et des and pour les ui
  } //TODO a faire correct en utilisant ltUI.

  val firstOfTwoUI: Fundef2[UI,UI,UI] ={
    val (xui, yui) = (p[UI]("xUI"), p[UI]("yUI"))
    Fundef2("firstOfTwoUI", xui, xui, yui)
  }



  val ltUI2: Fundef2[UI, UI, B] = {
    val (xui, yui) = (p[UI]("xminUI"), p[UI]("yminUI")); //a t-on x < y
    val difference = xui ^ yui //true for bits which differs betwen xui and yui
    val segmentOf1: Uint = Scan1(difference, orB, False(), Right(), initUsed = false) //fills with one, starting from the rightmost 1 to the first leftmost least significant bit
    //we have to affect segmentof1 because it is read simultaneously at two indexes, for first1.
    val first1: Uint = ~(new Call1[UI, UI](halveBUI, segmentOf1) with ASTBt[UI]) & segmentOf1 //only the rightmost msb bits remains. halveBui must comes first otherwise it bugs
    // true if yui is true for i being the index of the  with most significant bit of difference, that is a strict lower than
    Fundef2("ltUI", new Call1[UI, B](neqUI, first1 & yui) with ASTBt[B], xui, yui) //todo ecrire des xor et des and pour les ui
  } //TODO a faire correct en utilisant ltUI.


  /** optimal implementation of comparison between two unsigned integers, using orscanright like operators, missing just the first and final xor, so as to reuse first¯1, */
  val orScan: Fundef1[UI, UI] = {
    val difference = p[UI]("diff");
    val segmentOf1: Uint = Scan1(difference, orB, False(), Right(), initUsed = false) //fills with one, starting from the rightmost 1 to the first leftmost least significant bit
    Fundef1("orScan",segmentOf1, difference ) //todo ecrire des xor et des and pour les ui
  } //TODO a faire correct en utilisant ltUI.

  /** applied after orscan so as to identify the first true bit, which will be marked as one. Return null otherwise */
  val derivative: Fundef1[UI, UI] = {
    val segmentOf1 = p[UI]("segment");
    //we have to affect segmentof1 because it is read simultaneously at two indexes, for first1.
    val first1: Uint = ~(new Call1[UI, UI](halveBUI, segmentOf1) with ASTBt[UI]) & segmentOf1 //only the rightmost msb bits remains. halveBui must comes first otherwise it bugs
    // true if yui is true for i being the index of the  with most significant bit of difference, that is a strict lower than
    Fundef1("derivative",first1, segmentOf1 ) //todo ecrire des xor et des and pour les ui
  } //TODO a faire correct en utilisant ltUI.


  /** optimal implementation of comparison, reprogram ltUI2 in order to also output equality */
  val lteqUI2: Fundef2[UI, UI, B] = {
    val (xui, yui) = (p[UI]("xminUI"), p[UI]("yminUI")); //a t-on x < y
    val difference = xui ^ yui //true for bits which differs betwen xui and yui
    val segmentOf1: Uint = Scan1(difference, orB, False(), Right(), initUsed = false) //fills with one, starting from the rightmost 1 to the first leftmost least significant bit
    //we have to affect segmentof1 because it is read simultaneously at two indexes, for first1.
    val first1: Uint = ~(new Call1[UI, UI](halveBUI, segmentOf1) with ASTBt[UI]) & segmentOf1 //only the rightmost msb bits remains. halveBui must comes first otherwise it bugs
    // true if yui is true for i being the index of the  with most significant bit of difference, that is a strict lower than
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
  //type fakeRedop[R <: Ring] = (Fundef2RB[R], False)

  def ltUiRedop: redop[UI]=(ltUI2.asInstanceOf[Fundef2R[UI]],False().asInstanceOf[Uint])

  def concatRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
    (concatUI.asInstanceOf[Fundef2R[R]], Intof[UI](-1).asInstanceOf[ASTB[R]]) //neutral is wrong
  }
  def concatRedopold[R <: Ring](implicit n: repr[R]): redop[R] = {
    (concatB.asInstanceOf[Fundef2R[R]], Intof[UI](-1).asInstanceOf[ASTB[R]]) //neutral is wrong
  }

  def orRedop[R <: Ring](implicit n: repr[R]): redop[R] = {
    if (n.name.isInstanceOf[SI]) (orSI.asInstanceOf[Fundef2[R, R, R]], Intof[SI](-1).asInstanceOf[ASTB[R]])
    else if (n.name.isInstanceOf[UI]) (orUI.asInstanceOf[Fundef2[R, R, R]], Intof[UI](-1).asInstanceOf[ASTB[R]])
    else (orB.asInstanceOf[Fundef2[R, R, R]], False().asInstanceOf[ASTB[R]])
  }

  /** OrR2 will be allways true on the border */
  def or2Redop[R <: Ring](implicit n: repr[R]): redop[R] = {
    if (n.name.isInstanceOf[SI]) (orSI.asInstanceOf[Fundef2[R, R, R]], Intof[SI](-1).asInstanceOf[ASTB[R]])
    else if (n.name.isInstanceOf[UI]) (orUI.asInstanceOf[Fundef2[R, R, R]], Intof[UI](-1).asInstanceOf[ASTB[R]])
    else (orB.asInstanceOf[Fundef2[R, R, R]], True().asInstanceOf[ASTB[R]])
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
    //def maxSI = (new Call1[SI, SI](halveBSI, ASTB.Intof[SI](-1)(repr.nomSI)) with ASTBt[SI]) //halveBSI should enter a 1.
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

  /** by applying a xor, the period 010101 is doubled to OO11OO11 (and then to 000011110000....
   *  for some integer $p$, the input is of the form a sequence of bloc alternation 0^(2^p) 1^(2^p),
   * * alternation stops at some points either on zeroes or one ones.
   * * the output is of the same form, but with $p$ incremented
   * * the idea is that the output will change when the input goes from 1 to zero, and this happens twices less often
   * it  scans starting left, i.e from the least significant bits
   */
  val doublePeriod: Fundef1[UI,UI] = {
    val bcode = p[UI]("alt")
    Fundef1("doublePeriod",Scan1(bcode, xorB, False(), Left(), initUsed = false), bcode)
  }

  /** assuming the input if of the form 1* 0*, (a sequence of 1, followed by zeroes,
   * compute the parity of the number of ones.
   * It is simply the last bit of doublePeriod*/
  val parity: Fundef1[UI,B] = {
    val (bcode) = p[UI]("bcode")
    Fundef1("parity",Elt(-1,new Call1[UI,UI](doublePeriod,bcode)with ASTBt[UI] {}), bcode)
  }

 /** computes a 1 if and only if preceding bit is one, and current bit is zero
  * it uses a tailored function half called halfSIsurUI which behaves as if it would preserve the sign of a signed integer*/
  val clockGoingDown: Fundef1[UI,UI] = {
    val segmentsOf1 = p[UI]("segmentsOf1")
    val result: Uint = ~new Call1[UI, UI]( halfSIsurUI, segmentsOf1) with ASTBt[UI] & segmentsOf1 //only the rightmost msb bits remains. halveBui must comes first otherwise it bugs
  Fundef1("clockGoingDown",result, segmentsOf1)
  }

/** input is an unary sequence of up to 3 boolean.
 * It is a sequence of true followed by a sequence of false.
 * output is the binary code 100->10, 110->01, 111-> 11 */
  val unaryTonBbinary2: Fundef1R[UI] = {
    val (ucode) = p[UI]("ucode")
    val alt=new Call1[UI,UI](doublePeriod,ucode) with ASTBt[UI] {}
    val clockGoDo=new Call1[UI,UI](clockGoingDown,alt) with ASTBt[UI] {}
    val altClockGoDo=new Call1[UI,UI](doublePeriod,clockGoDo) with ASTBt[UI] {}
    val b0=Elt(-1,alt)
    val b1=Elt(-1,altClockGoDo )
    Fundef1("unaryCode2", b0::b1,ucode)
  }
  /** input is an unary sequence of up to seven boolean,
   * It is a sequence of true followed by a sequence of false.
   * output is the binary code 1000000->100, .... 1111111-> 111 */
  val unaryTonBbinary3: Fundef1R[UI] = {
    val (ucode) = p[UI]("ucode")
    val alt=new Call1[UI,UI](doublePeriod,ucode) with ASTBt[UI] {}
    val clockGoDo=new Call1[UI,UI](clockGoingDown,alt) with ASTBt[UI] {}
    val altClockGoDo=new Call1[UI,UI](doublePeriod,clockGoDo) with ASTBt[UI] {}
    val clockGoDoAltClockGoDo=new Call1[UI,UI](clockGoingDown,altClockGoDo) with ASTBt[UI] {}
    val altClockGoDoAltClockGoDo=new Call1[UI,UI](doublePeriod,clockGoDoAltClockGoDo) with ASTBt[UI] {}
    val b0=Elt(-1,alt)
    val b1=Elt(-1,altClockGoDo )
    val b2=Elt(-1,altClockGoDoAltClockGoDo)
    import compiler.repr.nomUI //ca favorise UI sur les autres et resoud une ambiguité
    Fundef1("unaryCode3", b0::b1::b2,ucode)
  }

}