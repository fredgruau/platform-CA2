package compiler

import ASTB.toBinary
import ASTB._
import ASTBfun._
import Circuit.{TabSymb, iTabSymb}
import org.scalatest.FunSuite

import scala.collection.immutable.HashMap

/** Test the correct implementation of integer operation, by evaluating them on samll integers */
class ASTBfunTest extends FunSuite {
  /** repeat last bits to reach the count of n. */
  def extend(n: Int, l: List[Boolean], v: Boolean) = l ::: List.fill(n - l.length)(v)

  def toInt(xs: List[Boolean]): Int = xs.foldRight(0)((x, y) => 2 * y + (if (x) 1 else 0))

  // def toASTB(x: Boolean) = if (x) true else false
  //def carryFromCode(x: Boolean, y: Boolean, z: Boolean) = eval(carry(toASTB(x), toASTB(y), toASTB(z)))
  // def fromASTB(x: Boolean, y: Boolean, z: Boolean, op: (ASTB[B], ASTB[B], ASTB[B]) => ASTB[B]) = eval(op(toASTB(x), toASTB(y), toASTB(z)));
  // def fromASTB(x: Boolean, y: Boolean, op: (ASTB[B], ASTB[B]) => ASTB[B]) = eval(op(toASTB(x), toASTB(y)));
  private def condReverseIn[T](l: List[T], d: Dir): List[T] = d match {
    case Right() => l.reverse
    case _ => l
  }

  private def condReverseOut[T](l: List[T], d: Dir): List[T] = d match {
    case Right() => l
    case _ => l.reverse
  }

  private def scan[T1, T2](init: T1, xs: List[T2], op: (T1, T2) => T1, d: Dir, initTaken: Boolean): List[T1] = {
    var result = if (initTaken) List(init) else List()
    var carry = init
    for (elt <- condReverseIn(xs, d)) {
      carry = op(carry, elt); result = carry :: result
    }
    condReverseOut(if (initTaken) result.tail else result, d) //le # bit reste le meme, parcequ'on enléve la derniere carry si y a init
  }

  def scanRight[T1, T2](init: T1, xs: List[T2], op: (T1, T2) => T1): List[T1] = {
    var result = List(init);
    var carry = init
    for (elt <- xs) {
      carry = op(carry, elt); result = carry :: result
    }
    result.tail
  }

  /** Forget the additional most significant new bits. */
  def scanLeft[T1, T2](init: T1, xs: List[T2], op: (T1, T2) => T1): List[T1] = {
    var result = List(init);
    var carry = init
    for (elt <- xs) {
      carry = op(carry, elt); result = carry :: result
    }
    result.tail.reverse
  } // the .tail forget the supplementary bit.

  import AST._

  private def eval(exp: AST[_], env: HashMap[Param[_], List[Boolean]]): List[Boolean] = exp match {
    case Call1(op, x) =>
      eval(op.arg, env + (op.p1 -> eval(x, env)))
    case Call2(op, x, y) =>
      eval(op.arg, env + (op.p1 -> eval(x, env)) + (op.p2 -> eval(y, env)))
    case Call3(op, x, y, z) => eval(op.arg, env + (op.p1 -> eval(x, env)) + (op.p2 -> eval(y, env)) + (op.p3 -> eval(z, env)))
    case u@Param(_) => env(u)
    case Mapp1(op, x) => eval(x.head, env).map(x1 => eval(op.arg, env + (op.p1 -> List(x1))).head)
    case Mapp2(x, y, op) => (eval(x, env), eval(y, env)).zipped.map((x1, y1) => eval(op.arg, env + (op.p1 -> List(x1)) + (op.p2 -> List(y1))).head)
    case Or(x, y) => List(eval(x, env).head | eval(y, env).head)
    case And(x, y) => List(eval(x, env).head & eval(y, env).head)
    case Xor(x, y) => List(eval(x, env).head ^ eval(y, env).head)
    case Neg(x) => List(!eval(x, env).head)
    case True() => List(true)
    case False() => List(false)
    case Intof(n) => val t = exp.mym.name.asInstanceOf[I];
      val nbit = nbitCte(n, t)
      val p = scala.math.pow(2, nbit).toInt;
      toBinary(n + (if (n >= 0) 0 else p), nbit)
    case Extend(n, exp) => val l = eval(exp, env); extend(n, l, if (exp.mym.name == UI()) false else l.last)
    case Elt(n, exp) => val l: List[Boolean] = eval(exp, env); List(if (n == -1) l.last else l(n))
    case Concat2(exp1, exp2) => eval(exp1, env) ::: eval(exp2, env)
    case Scan1(x, op: Fundef2R[B], v, dir, init) => scan[Boolean, Boolean](
      eval(v, env).head,
      eval(x, env),
      (u: Boolean, w: Boolean) => eval(op.arg, env + (op.p1 -> List(u)) + (op.p2 -> List(w))).head,
      dir, init)
    case Scan2(x, y, op, v, dir, init) => scan[Boolean, (Boolean, Boolean)](
      eval(v, env).head,
      (eval(x, env), eval(y, env)).zipped.map((x, y) => (x, y)),
      (u: Boolean, v: (Boolean, Boolean)) => v match {
        case (v1, v2) => eval(
          op.arg,
          env + (op.p1 -> List(u)) + (op.p2 -> List(v1)) + (op.p3 -> List(v2))).head
        case _ => throw new RuntimeException("operand of unequal number of bits");
      },
      dir, init)

  }

  val env = HashMap.empty[Param[_], List[Boolean]]

  //test constantes
  val trois = Intof[SI](3)
  val quatre = Intof[SI](4);
  test("quatre") {
    assert(eval(quatre, env) == List(false, false, true, false))
  }
  val cinq = Intof[SI](5)
  test("cinq") {
    assert(eval(cinq, env) == List(true, false, true, false))
  }
  test("Binary") {
    assert(toInt(toBinary(3, 5)) === 3)
  }

  //test inc opposé, soustraction, lt
  val six: ASTBt[SI] = new Call1[SI, SI](inc[SI], cinq) with ASTBt[SI] //note here that it is possible to go from UISI originally deliverd by inc, towards SI.
  test("Inc") {
    assert(toInt(eval(six, env)) === 6)
  }
  val mquatre = -quatre
  test("mquatre") {
    assert(eval(mquatre, env) == List(false, false, true, true))
  }
  val cinqmquatre = cinq - quatre
  test("cinqmquatre") {
    assert(eval(cinqmquatre, env) == List(true, false, false, false))
  }

  /*

    //test concat
    val zero = Intof[SI](0);  val mult8 =   trois :: zero :: zero :: zero
    test("ConcatMultiply"){assert(eval(mult8,env)==List(  false,false, false,true, true, false))}
  */

  //testLT
  val quatrelt0 = new Call1(ltSI, quatre) with ASTBt[B]
  test("quatre<0") {
    assert(eval(quatrelt0, env) == List(false))
  }
  /*
    val cinqLtquatre = new Call2(ltSI2Mod, cinq, quatre) with ASTBt[B]
    test("cinq<quatre") {
      assert(eval(cinqLtquatre, env) == List(false))
    }*/

  //test andLbtoR
  val quatreBis = True().&(quatre)(repr.nomSI)
  val false4 = False().&(quatre)(repr.nomSI)
  test("andLbtoRtrue") {
    assert(eval(quatreBis, env) == List(false, false, true, false))
  }
  test("andLbtoRfalse") {
    assert(eval(false4, env) == List(false, false, false, false))
  }

  //test cond et min
  /*
    val min4et5 = new Call2(minRelSI, quatre, cinq) with ASTBt[SI]
    val min5et4 = new Call2(minRelSI, cinq, quatre) with ASTBt[SI]

    test("cond et min") {
      assert(eval(min4et5, env) == List(false, false, true, false))
    }
    test("cond et min2") {
      assert(eval(min5et4, env) == List(false, false, true, false))
    }
    */
  //test extend
  val moins1 = Extend(4, Intof[SI](-1))
  //print( eval(moins1,env))
  val troisAs4m1 = quatre + moins1;
  test("add1") {
    assert(toInt(eval(troisAs4m1, env)) === 3)
  }

  //test fonction booleennes simple
  test("Carry") {
    assert(eval(Call3(carry, True(), True(), False()), env) === List(true))
    assert(eval(Call3(carry, True(), False(), False()), env) === List(false))
  }

  //test operation booléenne
  val sept = troisAs4m1 | quatre;
  test("Or") {
    assert(toInt(eval(sept, env)) === 7)
  }

  //test décalllage vers la gauche
  val quatrebis = Call1(halveB[SI], sept)
  test("Halve") {
    assert(toInt(eval(quatrebis, env)) == 3)
  }
  /*

    val oneStar=new Call1(orScanRightB.asInstanceOf[Fundef1R[SI]], mult8) with ASTBt[SI]
    test("orScanRight"){assert(eval(oneStar,env)==List( true, true, true ,true, true, false))}
  */


  //fonction utilisées dans bitify
  test("nBitR") {
    val nbitP = scala.collection.mutable.HashMap.empty[String, Int] //virgin, to retrieve the nbits computed for the param.
    val n = nbitExpAndParam(HashMap.empty[AST[_], Int], quatre, nbitP)
    assert(n == 4)
  }

}