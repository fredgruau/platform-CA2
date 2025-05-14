package progOfmacros

import compiler.AST._
import compiler.ASTBfun.Fundef2R
import compiler.ASTL._
import compiler.Circuit.iTabSymb
import compiler._

import scala.collection.immutable.HashMap

/** Aplique une comparaison, fonction de Ring Ring vers bool, sur un locus donné.  */
object Cmp {

  private var cmpmem: iTabSymb[Fundef2[(Locus, Ring),(Locus, Ring),(Locus, B) ]] = HashMap()

  /** prefix contains the family name "cmp", and the name. the suffix stores locus and ring of both operands.  */
  private def cmpfunName[L<:Locus, R <: Ring](op:Fundef2[Ring,Ring,B], l:Locus)(implicit m: repr[L],  q: repr[R]) = {
    val y = 0
    ("" + "cmp" + op.name + "." + l.shortName+q.name).toLowerCase.dropRight(2)
  }
  private def cmpfunDef[L <: Locus, R <: Ring](op: Fundef2[R,R,B], l: L )(implicit m: repr[L],  q: repr[R]): //pour defVe S1=E,S2=V
  Fundef2[(L, R), (L, R), (L, B)] = {
    val param1 = pL[L, R](("p" + l.shortName + q.name).dropRight(2)) //parameter names inform about locus
    val param2 = pL[L, R](("q" + l.shortName + q.name).dropRight(2)) //parameter names inform about locus
    Fundef2(cmpfunName(op, l)(m,q), binop(op,param1,param2),param1,param2) // we compute a function of one argument. res is the body, param are the single parameter
  }

  def getCmpFun[L <: Locus, R <: Ring](op:Fundef2[Ring,Ring,B], l: L ) (implicit m:repr[L],q:repr[R]) = {
    val funName = cmpfunName(op, l)(m,q)
    if (!cmpmem.contains(funName)) //redSmem memoizes so that we 'd compile the function only once.
      cmpmem = cmpmem + (funName -> cmpfunDef(op, l))
    cmpmem(funName).asInstanceOf[ Fundef2[(L,R),(L,R),(L,B)] ]
  }

}
