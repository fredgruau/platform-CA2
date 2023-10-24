package progOfmacros

import compiler.AST._
import compiler.ASTBfun.{andRedop, minRedop, minUI, orRedop, p, redop, xorRedop}
import compiler.ASTL._
import compiler.Circuit.iTabSymb
import compiler.repr.{nomB, nomCons, nomV}
import compiler.{AST, ASTLt, B, E, F, Ring, S, SI, T, UI, V, chipBorder, repr}
import progOfmacros.RedS.getRedSFun

import scala.collection.immutable.HashMap

object RedS {
  /*
    /** memoizes all the already used Boolean reduction */
    private var redSmemOld: iTabSymb[Fundef1[(S, B), (S, B)]] = HashMap()

    private def redsfunNameOld[S1 <: S, S2 <: S](r: redop[B], l: S1)(implicit m: repr[S1], n: repr[S2]) = {
      val y = 0
      ("" + "redS." + r._1.name + l.shortName + n.name.shortName).toLowerCase
    }

   private def redSfunDefOld[S1 <: S, S2 <: S](r: redop[B], l: S1)(implicit m: repr[S1], n: repr[S2], d: chipBorder[S2, S1]): //pour defVe S1=E,S2=V
    Fundef1[(S1, B), (S2, B)] = {
      val param = p[S1, B]("p" + l.shortName + n.name.shortName) //parameter names inform about locus
      val broadcasted = broadcast[S1, S2, B](param) //step 1 is broadcast
      val transfered: ASTLt[T[S2, S1], B] = transfer[S1, S2, B](broadcasted)(repr.nomT(n, m), repr.nomB) //step 2 is transfer
      val res = reduce[S2, S1, B](r, transfered) //(n,m,d) yzeté implicit killerest
      //val res = Redop[S2, S1, B](r, transfered, n, nomB) // orRdef(transfer(v(param))) //step 3 is reduce
      Fundef1(redsfunNameOld(r, l)(m, n), res, param) // we compute a function of one argument. res is the body, param are the single parameter
    }


    def getRedSFunOld[S1 <: S, S2 <: S](r: redop[B], l: S1)(implicit m: repr[S1], n: repr[S2], d: chipBorder[S2, S1]): Fundef1[(S1, B), (S2, B)] = {
      val funName = redsfunNameOld(r, l)(m, n)
      if (!redSmem.contains(funName))
        redSmem = redSmem + (funName -> redSfunDefOld(r, l)(m, n, d))
      redSmem(funName).asInstanceOf[Fundef1[(S1, B), (S2, B)]]
    }
  */

  /** memoizes all the already used Boolean reduction */
  private var redSmem: iTabSymb[Fundef1[(S, Ring), (S, Ring)]] = HashMap()

  /** how to build the name of simplicial reduction. The name informs about
   * name of the file where macro is to be stored
   * source and target simplicial locus, as well as reduction operation */
  private def redsfunName[S1 <: S, S2 <: S, R <: Ring](r: redop[R], l: S1)(implicit m: repr[S1], n: repr[S2], p: repr[R]) = {
    val y = 0
    ("" + "redS." + r._1.name + l.shortName + n.name.shortName).toLowerCase
  }

  /**
   *
   * @param r
   * @param l
   * @param m
   * @param n
   * @param d
   * @tparam S1 source simplicial type
   * @tparam S2 target simplicial type
   * @return computes the scala code of a whole  simplicial reduction, is done here because Broadcast Transfer and Redop are private to ASTL. */

  private def redSfunDef[S1 <: S, S2 <: S, R <: Ring](r: redop[R], l: S1)(implicit m: repr[S1], n: repr[S2], q: repr[R], d: chipBorder[S2, S1]): //pour defVe S1=E,S2=V
  Fundef1[(S1, R), (S2, R)] = {
    val param = p[S1, R]("p" + l.shortName + n.name.shortName) //parameter names inform about locus
    val broadcasted = broadcast[S1, S2, R](param) //step 1 is broadcast
    val transfered: ASTLt[T[S2, S1], R] = transfer[S1, S2, R](broadcasted)(repr.nomT(n, m), q) //step 2 is transfer
    val res = reduce[S2, S1, R](r, transfered) //(n,m,d) yzeté implicit killerest
    //val res = Redop[S2, S1, B](r, transfered, n, nomB) // orRdef(transfer(v(param))) //step 3 is reduce
    Fundef1(redsfunName(r, l)(m, n, q), res, param) // we compute a function of one argument. res is the body, param are the single parameter
  }

  /**
   *
   * @param S1 origine simplicial type
   * @param S2 target simplicial type
   * @param r  reduction applied
   * @return function in scala which does the corresponding simplicial reduction,  memoised in redSmem
   */
  def getRedSFun[S1 <: S, S2 <: S, R <: Ring](r: redop[R], l: S1)(implicit m: repr[S1], n: repr[S2], q: repr[R], d: chipBorder[S2, S1]): Fundef1[(S1, R), (S2, R)] = {
    val funName = redsfunName(r, l)(m, n, q)
    if (!redSmem.contains(funName))
      redSmem = redSmem + (funName -> redSfunDef(r, l)(m, n, q, d))
    redSmem(funName).asInstanceOf[Fundef1[(S1, R), (S2, R)]]
  }
  /** wrapper to a function built on the fly
   *
   * @return a call to an or reduction, exist is a more explicit name
   *         pour defEv S1=E S2=V, the type of chipBorder is Ve therefore [S2, S1] */
  def exist[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2], d: chipBorder[S2, S1]): ASTLt[S2, B] = {
    val f: Fundef1[(S1, B), (S2, B)] = getRedSFun(orRedop[B], arg.locus)(m, n, nomB, d)
    new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
  }


  def leastUI[S1 <: S, S2 <: S](arg: ASTLt[S1, UI])(implicit m: repr[S1], n: repr[S2], d: chipBorder[S2, S1]): ASTLt[S2, UI] = {
    val f: Fundef1[(S1, UI), (S2, UI)] = getRedSFun(minRedop[UI], arg.locus)(m, n, repr.nomUI, d)
    new Call1[(S1, UI), (S2, UI)](f, arg)(repr.nomLR(n, compiler.repr.nomUI)) with ASTLt[S2, UI] {}
  }

  /*
    /** @return a call to an and reduction, inside is a more explicit name */
    def inside[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2]): ASTLt[S2, B] = {
      val f = getRedSFun(andRedop(repr.nomB), arg.locus)(m, n)
      new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
    }

    /** @return a call to an xor reduction, frontier is a more explicit name */
    def frontier[S1 <: S, S2 <: S](arg: ASTLt[S1, B])(implicit m: repr[S1], n: repr[S2]): ASTLt[S2, B] = {
      val f = getRedSFun(xorRedop(repr.nomB), arg.locus)(m, n)
      new Call1[(S1, B), (S2, B)](f, arg)(repr.nomLR(n, compiler.repr.nomB)) with ASTLt[S2, B] {}
    }*/

  /*
  def v[S1 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, V]], n: repr[R]): Broadcast[S1, V, R] =
  Broadcast[S1, V, R](arg, m, n); // for broadcast, we want to specify only the direction where broadcasting takes place.


  def orRdef[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] =
    Redop[S1, S2, R](orRedop[R], arg, m, n)


    case class Caall1[Ti1, To1](override val f: Fundef1[Ti1, To1], arg: AST[_ <: Ti1])(implicit n: repr[To1])

    def aaaandR[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): Redop[S1, S2, R] =
      Redop[S1, S2, R](andRedop[R], arg, m, n)


    /** From a boolE, computes adjacent vertices */
    val existFun: Fundef1[(E, B), (V, B)] = {
      val e = p[E, B]("edge")
      val existV: BoolV = orRdef(transfer(v(e)))
      existV.setName("existV");
      Fundef1("existE2V", existV, e)
    }*/

}
