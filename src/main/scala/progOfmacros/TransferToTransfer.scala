package progOfmacros

import compiler.AST._
import compiler.ASTBfun.redop
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.iTabSymb
import compiler._

import scala.collection.immutable.HashMap

/** allows to automatically generate macro for simplicial reductions */
object TransferToTransfer {
  /** memoizes all the already used Boolean reduction */
  private var tttmem: iTabSymb[Fundef1[(T[S,S], Ring), (T[S,S], Ring) ]] = HashMap()

  /** how to build the name of simplicial reduction. The prefix ofthe name (until the point) informs about
   * name of the file where macro is to be stored
   * source and target simplicial locus, as well as reduction operation */
  private def tttfunName[S1 <: S, S2 <: S, R <: Ring]( l: T[S1,S2])(implicit m: repr[S1], n: repr[S2], p: repr[R]) = {
    val y = 0
    ("" + "ttt"+ "."  + l.shortName  ).toLowerCase
  }


  /**
   *
   * @param r
   * @param l
   * @param m
   * @param n
   * @param d  constant layer defining neighborhood which are undefined
   * @tparam S1 source simplicial type
   * @tparam S2 target simplicial type
   * @return computes the scala code of a whole  simplicial reduction, is done here because Broadcast Transfer and Redop are private to ASTL. */
  def mytransfer[S1 <: S, S2 <: S, R <: Ring]( arg: ASTLt[T[S1,S2], R])
                                             (implicit m: repr[S1], n: repr[S2], q: repr[R], d: chip[S2, S1]): ASTLt[T[S2,S1], R] = {
   // val broadcasted = broadcast[S1, S2, R](arg) //step 1 is broadcast
    val transfered: ASTLt[T[S2, S1], R] = transfer[S1, S2, R](arg)(repr.nomT(n, m), q) //step 2 is transfer
   transfered
  }
  /**
   *
   * @tparam S1 source
   * @tparam S2 target
   * @return
   */
  private def tttfunDef[S1 <: S, S2 <: S, R <: Ring](l: T[S1,S2])(implicit m: repr[S1], n: repr[S2], q: repr[R], d: chip[S2, S1]): //pour defVe S1=E,S2=V
  Fundef1[(T[S1,S2], R), (T[S2,S1], R)] = {
    val param = pL[T[S1,S2], R]("p" + l.shortName + n.name.shortName) //parameter names inform about locus
    Fundef1(tttfunName( l)(m, n, q), mytransfer[S1, S2, R]( param), param) // we compute a function of one argument. res is the body, param are the single parameter
  }

  /**
   *
   * @param S1 origine simplicial type
   * @param S2 target simplicial type
   * @param r  reduction applied
   * @return function in scala which does the corresponding simplicial reduction,  memoised in redSmem
   */
  def getttFun[S1 <: S, S2 <: S, R <: Ring]( l: T[S1,S2])(implicit m: repr[S1], n: repr[S2], q: repr[R], d: chip[S2, S1]):
      Fundef1[(T[S1,S2], R), (T[S2,S1], R)] = {
    val funName = tttfunName( l)(m, n, q)
    if (!tttmem.contains(funName)) //redSmem memoizes so that we 'd compile the function only once.
      tttmem = tttmem + (funName -> tttfunDef( l)(m, n, q, d))
    tttmem(funName).asInstanceOf[Fundef1[(T[S1,S2], R), (T[S2,S1], R)]]
  }




}
