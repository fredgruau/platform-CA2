package progOfmacros

import compiler.AST._
import compiler.ASTBfun.{Fundef2R, redop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.iTabSymb
import compiler._
import progOfmacros.RedD.{redfunDef, redfunName, redmem}

import scala.collection.immutable.HashMap

/** allow to automatically generates direct reductions */
object RedD {
  /** memoizes all the already used Boolean reduction */
  private var redmem: iTabSymb[Fundef1[(T[S,S], Ring), (S, Ring)]] = HashMap()

  /** how to build the name of simplicial reduction. The prefix ofthe name (until the point) informs about
   * name of the file where macro are defined: "Redd" , as well as the reduction operation. Suffix indicate locus
   * source and target simplicial locus,  */
  private def redfunName[S1 <: S, S2 <: S, R <: Ring](r: redop[R], l: S1)(implicit m: repr[S1], n: repr[S2], p: repr[R]) = {
    val y = 0
    ("" + "redd" + r._1.name + "." + n.name.shortName + l.shortName ).toLowerCase  //a file contains different locus for a given reduction and ring type in B,I for boolean or integer
  }

  /**
   * @tparam S1 lower case simplicial type E
   * @tparam S2 target simplicial type V
   *    réduit directement de T[S2,S1] vers S2, (permet de simplifier le code) todo: y enlever les defVe)
   *                      **/
  private def redfunDef[S1 <: S, S2 <: S, R <: Ring](r: redop[R], l: S1)(implicit m: repr[S1], n: repr[S2], q: repr[R], d: chip[S2, S1]): //pour defVe S1=E,S2=V
  Fundef1[(T[S2,S1], R), (S2, R)] = {
    val param = pL[T[S2,S1], R]("p" + l.shortName + n.name.shortName) //parameter names inform about locus
    Fundef1(redfunName(r, l)(m, n, q), reduce[S2, S1, R](r, param), param) // we compute a function of one argument. res is the body, param are the single parameter
  }

  /**
   *
   * @param S1 origine simplicial type E
   * @param S2 target simplicial type V
   * @param r  reduction applied
   * @return function in scala which does the corresponding simplicial reduction,  memoised in redSmem
   */
  def getRedFun[S1 <: S, S2 <: S, R <: Ring](r: redop[R], l: S1)(implicit m: repr[S1], n: repr[S2], q: repr[R], d: chip[S2, S1]):  Fundef1[(T[S2,S1], R), (S2, R)]  = {
    val funName = redfunName(r, l)(m, n, q)
    if (!redmem.contains(funName)) //redSmem memoizes so that we 'd compile the function only once.
      redmem = redmem + (funName -> redfunDef(r, l)(m, n, q, d))
    redmem(funName).asInstanceOf[ Fundef1[(T[S2,S1], R), (S2, R)] ]
  }


}
