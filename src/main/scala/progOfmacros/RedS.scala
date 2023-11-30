package progOfmacros

import compiler.AST._
import compiler.ASTBfun.{andRedop, concatRedop, minRedop, minUI, orRedop, redop, xorRedop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.iTabSymb
import compiler.repr.{nomB, nomCons, nomV}
import compiler.{AST, ASTLt, B, E, F, Ring, S, SI, T, UI, V, chip, repr}
import progOfmacros.RedS.getRedSFun

import scala.collection.immutable.HashMap

object RedS {
  /** memoizes all the already used Boolean reduction */
  private var redSmem: iTabSymb[Fundef1[(S, Ring), (S, Ring)]] = HashMap()

  /** how to build the name of simplicial reduction. The prefix ofthe name (until the point) informs about
   * name of the file where macro is to be stored
   * source and target simplicial locus, as well as reduction operation */
  private def redsfunName[S1 <: S, S2 <: S, R <: Ring](r: redop[R], l: S1)(implicit m: repr[S1], n: repr[S2], p: repr[R]) = {
    val y = 0
    ("" + "redS" + r._1.name + "." + l.shortName + n.name.shortName).toLowerCase
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

  private def redSfunDef[S1 <: S, S2 <: S, R <: Ring](r: redop[R], l: S1)(implicit m: repr[S1], n: repr[S2], q: repr[R], d: chip[S2, S1]): //pour defVe S1=E,S2=V
  Fundef1[(S1, R), (S2, R)] = {
    val param = pL[S1, R]("p" + l.shortName + n.name.shortName) //parameter names inform about locus
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
  def getRedSFun[S1 <: S, S2 <: S, R <: Ring](r: redop[R], l: S1)(implicit m: repr[S1], n: repr[S2], q: repr[R], d: chip[S2, S1]): Fundef1[(S1, R), (S2, R)] = {
    val funName = redsfunName(r, l)(m, n, q)
    if (!redSmem.contains(funName))
      redSmem = redSmem + (funName -> redSfunDef(r, l)(m, n, q, d))
    redSmem(funName).asInstanceOf[Fundef1[(S1, R), (S2, R)]]
  }


}
