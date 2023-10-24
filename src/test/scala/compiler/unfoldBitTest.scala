package compiler

import AST.Call2
import ASTB._
import ASTBfun._
import Circuit.{TabSymb, iTabSymb}
import VarKind.MacroField
import dataStruc.{Dag, DagInstr}
import org.scalatest.FunSuite

import scala.collection.immutable.HashMap
import scala.collection.mutable

/** Test the correct implementation of integer operation, by evaluating them */
class unfoldBitTest extends FunSuite {


  /////////////////////////////////////////////////////////////////////////
  /** repeat last bits to reach the count of n. */

  import AST._

  /////////////////////////////////////////////////////////////////////////
  val env2 = HashMap.empty[String, List[ASTBt[B]]]
  val infoo = new InfoNbit(SI(), MacroField(), 3)
  val infoo2 = new InfoNbit(SI(), MacroField(), 2)
  val tsymb: TabSymb[InfoNbit[_]] = mutable.HashMap("toto" -> infoo, "tata" -> infoo, "sign" -> infoo2, "tutu" -> infoo2)
  val m2 = Intof[SI](-2);
  val zero = Extend(3, Intof[SI](0))
  /* test("IntOf") {
     assert(m2.unfoldBit(env2, tsymb) == List(False(), True()))
   }*/
  val m2e: ASTBt[SI] = Extend(3, m2)
  /*test("extend") {
    assert(m2e.unfoldBit(env2, tsymb) == List(False(), True(), True()))
  }*/
  val toto = new Read[SI]("toto") with ASTBt[SI]
  /*test("read") {
    assert(toto.unfoldBit(env2, tsymb).map(_.asInstanceOf[Read[_]].which) == List("toto0", "toto1", "toto2"))
  }*/
  val tata = new Read[SI]("tata") with ASTBt[SI]
  val sign2 = new Read[SI]("sign") with ASTBt[SI]
  val totoa = tata | toto
  /*test("pure symbol") {
    assert((totoa.unfoldBit(env2, tsymb)).map(_.toStringTree).toString ==
      "List(| (tata0  , toto0  ), | (tata1  , toto1  ), | (tata2  , toto2  ))")}*/
  val totor: ASTBt[SI] = toto | m2e
  /*test("mixSymbolwithBooland simplify where possible") {
    assert((totor.unfoldBit(env2, tsymb)).toString == "List(toto0, truue, truue)")
  }*/


  val exprMapScan = -toto
  val env3 = HashMap.empty[String, ASTBg]
  val mapscan: ASTBg = exprMapScan.deCallify(env3)
  test("deCallify") {
    assert(mapscan.toStringTree == "Mapp2xorB (Scan1andBLeft() Mapp1negB (toto  ), Mapp1negB (toto  ))")
  }

  val totop1 = (new Call1[SI, SI](incSI.asInstanceOf[Fundef1R[SI]], toto) with ASTBt[SI])
  /** to test that left and right loop can be separated */
  val twoWays = (new Call1[SI, SI](orScanRightB.asInstanceOf[Fundef1R[SI]], totop1) with ASTBt[SI])
  //A present on se lance dans le affectify d'une expression simple: Mapscan
  val abs = new Call2[SI, SI, SI](minRelSI, toto, -toto) with ASTBt[SI]
  val lemin = new Call2[SI, SI, SI](minRelSI, toto, tata) with ASTBt[SI]
  val signm2e = new Call1[SI, SI](sign, m2e) with ASTBt[SI]

  val signtata = new Call1[SI, SI](sign, -tata) with ASTBt[SI]

  val sign1 = Intof[SI](1);
  val signm1 = Extend(2, Intof[SI](-1))
  val signMin = new Call2[SI, SI, SI](minSign, sign1, signm1) with ASTBt[SI]
  val signMin2 = new Call2[SI, SI, SI](minSign, sign1, signm1) with ASTBt[SI]
  val totom2 = toto + m2e
  val negm2e = ~m2e
  val negnegm2e = ~negm2e
  val totogt = toto < tata

  val signtotom2 = new Call1[SI, SI](sign, totom2) with ASTBt[SI]
  val testMinSign = new Call2[SI, SI, SI](minRelSI, signtotom2, sign2) with ASTBt[SI]
/*  test("codeGen") {
    val cod = new CodeGen(tsymb)
    // autre test effectués -toto totop1 (tata+toto) (tata-toto) (tata<=toto) (twoWays) -toto abs m2e signm2e lemin signMin totom2 totogt signtata
    val res = cod.boolifyInstr(new Affect("tutu", totogt).asInstanceOf[Affect[ASTBg]])
    val res2 = res.map(_.map(_.toStringTree).mkString("|_____|"))
    println(cod.loops)
    println("________________\n" + res2.mkString("\n"))
    print(cod.isBoolConstant)
  }*/


  test("slice") { //print((toto-tata).deCallify(env3, tsymb).toStringTree)
    //   assert(twoWays.deCallify(env3, tsymb).toString ==
  }
}