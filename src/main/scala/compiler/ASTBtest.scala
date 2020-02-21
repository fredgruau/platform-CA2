package compiler

import compiler.ASTB._
import compiler.ASTBfun._
import junit.framework.TestCase

import junit.framework.Assert.assertEquals
import junit.framework.Assert.fail
import ASTB._
import ASTBfun._
import scala.collection.immutable.HashMap

/**Test the correct implementation of integer operation, by evaluating them */
class ASTBtest extends TestCase {
  /**repeat last bits to reach the count of n. */
  Array.fill[Byte](5)(0)
  List.fill[Int](5)(0)
  def extend (n:Int, l:List[Boolean],v:Boolean)=l:::List.fill(n-l.length)(v)
  def toBinaryPos(n:Int) = toBinary(n, log2(n))
  
  /** Binary code, LSB at head */
  def toBinary(n: Int, size: Int): List[Boolean] =
    if (size == 0) List() else (if (n % 2 == 1) true else false) :: toBinary(n / 2, size - 1)

  def toInt(xs: List[Boolean]): Int = xs.foldRight(0)((x, y) => 2 * y + (if (x) 1 else 0))
  // def toASTB(x: Boolean) = if (x) True() else False()
  //def carryFromCode(x: Boolean, y: Boolean, z: Boolean) = eval(carry(toASTB(x), toASTB(y), toASTB(z)))
  // def fromASTB(x: Boolean, y: Boolean, z: Boolean, op: (ASTB[B], ASTB[B], ASTB[B]) => ASTB[B]) = eval(op(toASTB(x), toASTB(y), toASTB(z)));
  // def fromASTB(x: Boolean, y: Boolean, op: (ASTB[B], ASTB[B]) => ASTB[B]) = eval(op(toASTB(x), toASTB(y)));
  private def condReverseIn[T](l: List[T], d: Dir): List[T] = d match { case Right() => l.reverse case _ => l }
  private def condReverseOut[T](l: List[T], d: Dir): List[T] = d match { case Right() => l case _ => l.reverse }
  private def scan[T1, T2](init: T1, xs: List[T2], op: (T1, T2) => T1, d: Dir, initTaken: Boolean): List[T1] = {
    var result = if (initTaken) List(init) else List()
    var carry = init
    for (elt <- condReverseIn(xs, d)) { carry = op(carry, elt); result = carry :: result }
    condReverseOut(if (initTaken) result.tail else result, d) //le # bit reste le meme, parcequ'on enléve la derniere carry si y a init
  }

  def scanRight[T1, T2](init: T1, xs: List[T2], op: (T1, T2) => T1): List[T1] = {
    var result = List(init); var carry = init
    for (elt <- xs) { carry = op(carry, elt); result = carry :: result }
    result.tail
  }
  /**Forget the additional most significant new bits. */
  def scanLeft[T1, T2](init: T1, xs: List[T2], op: (T1, T2) => T1): List[T1] = {
    var result = List(init); var carry = init
    for (elt <- xs) { carry = op(carry, elt); result = carry :: result }
    result.tail.reverse
  } // the .tail forget the supplementary bit.
  import AST._

  private def eval(exp: AST[_], env: HashMap[Param[_], List[Boolean]]): List[Boolean] = exp match {
    case Call1(op, x)            => eval(op.arg, env + (op.p1 -> eval(x, env)))
    case Call2(op, x, y)         => eval(op.arg, env + (op.p1 -> eval(x, env)) + (op.p2 -> eval(y, env)))
    case Call3(op, x, y, z)      => eval(op.arg, env + (op.p1 -> eval(x, env)) + (op.p2 -> eval(y, env)) + (op.p3 -> eval(z, env)))
    case u @ Param(_)            => env(u)
    case Mapp2(x, y, op)         => (eval(x, env), eval(y, env)).zipped.map((x1, y1) => eval(op.arg, env + (op.p1 -> List(x1)) + (op.p2 -> List(y1))).head)
    /*case Or(x, y)                => List(eval(x, env).head | eval(y, env).head)
    case And(x, y)               => List(eval(x, env).head & eval(y, env).head)
    case Xor(x, y)               => List(eval(x, env).head ^ eval(y, env).head)*/
      case Or(x, y)                      => (eval(x, env), eval(y, env)).zipped.map(_ | _)
    case And(x, y)                     => (eval(x, env), eval(y, env)).zipped.map(_ & _)
    case Xor(x, y)                     => (eval(x, env), eval(y, env)).zipped.map(_ ^ _)
    //case ConstSignedInt(n, size) => toBinary(n, size)

   case Boolof(v)                  => List(v) 

    case Intof(n ) => val t=exp.mym.name.asInstanceOf[I]; val nbit= nbitCte(n,t)
      val p=scala.math.pow(2,nbit).toInt;    toBinary (n+(if(n>=0)0 else p  ) ,nbit)
    
    
     case Extend(n,exp)  =>  val l= eval(exp,env);extend(n,l,  if(exp.mym.name==UI()) false else l.last)
    
    case Scan1(x, op, v, dir, init) => scan[Boolean, Boolean](
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

    /* case ScanLeft2Init2(x, y, op, v) => scanLeft[Boolean, (Boolean, Boolean)](
      eval(v, env).head,
      (eval(x, env), eval(y, env)).zipped.map((x, y) => (x, y)),
      (u: Boolean, v: (Boolean, Boolean)) => v match {
        case (v1, v2) => eval(
          op.arg,
          (env + (op.p1 -> List(u))
            + (op.p2 -> List(v1))
            + (op.p3 -> List(v2)))).head
        case _ => throw new RuntimeException("operand of unequal number of bits");
      })
    case ScanLeft1Init(x, op, v) => scanLeft[Boolean, Boolean](
      eval(v, env).head,
      eval(x, env), (u: Boolean, w: Boolean) => eval(op.arg, env + (op.p1 -> List(u)) + (op.p2 -> List(w))).head)
    case ScanRight2(x, y, op, v) => scanRight[Boolean, (Boolean, Boolean)](
      eval(v, env).head,
      (eval(x, env).reverse, eval(y, env).reverse).zipped.map((x, y) => (x, y)),
      (u: Boolean, v: (Boolean, Boolean)) => v match { case (v1, v2) => eval(op.arg, (env + (op.p1 -> List(u)) + (op.p2 -> List(v1)) + (op.p3 -> List(v2)))).head })
    // case _ => List(true, false)*/
  }
  val env = HashMap.empty[Param[_], List[Boolean]]
  def testBinary() {   assertEquals(toInt(toBinary(3, 5)), 3) }
  def testCarry() {
    assertEquals(eval(Call3(carry, true,true,false), env), List(true))
    assertEquals(eval(Call3(carry, true,false,false), env), List(false))
  } 
  val quatre = Intof[SI](4 ); val moins1 = Extend(4,Intof[SI](-1))
  //print( eval(moins1,env))
  val trois =  quatre + moins1 ;
  def testadd1() { assert(toInt(eval(trois, env)) == 3) }
  val sept  =  trois | quatre ;
  def testOr() { assert(toInt(eval(sept, env)) == 7) }
    val six = trois+trois

  def testAdd2() { assert(toInt(eval(six, env)) == 6) }
  val septbis:ASTBt[SI]= new Call1(inc .asInstanceOf[Fundef1R[SI]], six) with ASTBt[SI]  //note here that it is possible to go from UISI originally deliverd by inc, towards SI. 
  def testInc() { assert(toInt(eval(septbis, env)) == 7) }
  val quatrebis = Call1(halveB.asInstanceOf[Fundef1R[SI]], sept) 
  def testHalve() { assert(toInt(eval(quatrebis, env)) == 3) }
  val grand = Intof[SI](15 )

  def testComputeNbit() {  val nbitP = scala.collection.mutable.HashMap.empty[Param[_], Int] //virgin, to retrieve the nbits computed for the param.
      val n = nBitR(HashMap.empty[AST[_], Int], quatre,nbitP)
    assert(n == 4)
  }
}