package progOfmacros

import compiler.AST._
import compiler.ASTBfun.{Fundef2R, redop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.iTabSymb
import compiler._

import scala.collection.immutable.HashMap
/** Construit des macro trés simple qui applique juste un operateur binaire, cela évite d'avoir a générer des fundef anonymes, tout le temps.
 * et rends le code plus lisibles.  */
object Bino {

  private var binmem: iTabSymb[Fundef2[(Locus, Ring),(Locus, Ring),(Locus, Ring) ]] = HashMap()

  /** prefix contains the family name "bino", and the name. the suffix stores locus and ring of both operands.  */
  private def binfunName[L<:Locus, R <: Ring](op:Fundef2R[R], l:Locus)(implicit m: repr[L],  q: repr[R]) = {
    val y = 0
    ("" + "bino" + op.name + "." + l.shortName+q.name).toLowerCase.dropRight(2)
  }
  private def binfunDef[L <: Locus, R <: Ring](op: Fundef2R[R], l: L )(implicit m: repr[L],  q: repr[R]): //pour defVe S1=E,S2=V
  Fundef2[(L, R), (L, R), (L, R)] = {
    val param1 = pL[L, R](("p" + l.shortName + q.name).dropRight(2)) //parameter names inform about locus
    val param2 = pL[L, R](("q" + l.shortName + q.name).dropRight(2)) //parameter names inform about locus

    Fundef2(binfunName(op, l)(m,q), binop(op,param1,param2),param1,param2) // we compute a function of one argument. res is the body, param are the single parameter
  }

  def getBinFun[L <: Locus, R <: Ring](op: Fundef2R[R], l: L ) (implicit m:repr[L],q:repr[R]) = {
    val funName = binfunName(op, l)(m,q)
    if (!binmem.contains(funName)) //redSmem memoizes so that we 'd compile the function only once.
      binmem = binmem + (funName -> binfunDef(op, l))
    binmem(funName).asInstanceOf[ Fundef2[(L,R),(L,R),(L,R)] ]
  }

}
