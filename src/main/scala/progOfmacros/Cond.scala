package progOfmacros

import compiler.AST._
import compiler.ASTL._
import compiler.ASTLfun.cond
import compiler.Circuit.iTabSymb
import compiler._

import scala.collection.immutable.HashMap

/** Aplique une comparaison, fonction de Ring Ring vers bool, sur un locus donné.  */
object Cond {

  private var condmem: iTabSymb[Fundef3[(Locus, B),(Locus, Ring),(Locus, Ring),(Locus, Ring) ]] = HashMap()

  /** prefix contains the family name "cmp", and the name. the suffix stores locus and ring of both operands.  */
  private def condfunName[L<:Locus, R <: Ring]( l:Locus)(implicit m: repr[L],  q: repr[R]) = {
    val y = 0
    ("" + "cond" +  "." + l.shortName+q.name).toLowerCase.dropRight(2)
  }
  private def condfunDef[L <: Locus, R <: Ring]( l: L )(implicit m: repr[L],  q: repr[R]): //pour defVe S1=E,S2=V
  Fundef3[(L, B), (L, R), (L, R), (L, R)] = {
    val param0 = pL[L, B](("c" + l.shortName + q.name).dropRight(2))
    val param1 = pL[L, R](("p" + l.shortName + q.name).dropRight(2)) //parameter names inform about locus
    val param2 = pL[L, R](("q" + l.shortName + q.name).dropRight(2)) //parameter names inform about locus
    Fundef3(condfunName( l)(m,q), cond(param0,param1,param2),param0,param1,param2) // we compute a function of one argument. res is the body, param are the single parameter
  }

  def getCondFun[L <: Locus, R <: Ring]( l: L ) (implicit m:repr[L],q:repr[R]) = {
    val funName = condfunName( l)(m,q)
    if (!condmem.contains(funName)) //redSmem memoizes so that we 'd compile the function only once.
      condmem = condmem + (funName -> condfunDef( l))
    condmem(funName).asInstanceOf[ Fundef3[(L,B),(L,R),(L,R),(L,R)] ]
  }

}
