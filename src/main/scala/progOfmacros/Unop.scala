package progOfmacros

import compiler.AST.{Fundef1, pL}
import compiler.ASTL.unop
import compiler.Circuit.iTabSymb
import compiler.{Locus, Ring, repr}

import scala.collection.immutable.HashMap
/** uses to automatically compile the java code of unop */
object Unop {

  object Unop{
    private var unopmem: iTabSymb[Fundef1[(Locus, Ring), (Locus, Ring)]] = HashMap()
    /** how to build the name of the unop funciton
     * prefix unform of the name of the file  where the macro is defined: unop as well as the operator itself
     * suffix inform on solely the locus. */
    private def unopfunName[L<:Locus, Ri <: Ring,Ro<:Ring](o:Fundef1[Ri,Ro], l:L)(implicit  ri: repr[Ri], ro: repr[Ro]) = {
      val y = 0
      ("" + "unop" + o.name + "." +  l.shortName ).toLowerCase
    }

    private def unopfunDef[L<:Locus, Ri <: Ring,Ro<:Ring](o:Fundef1[Ri,Ro], l: L)(implicit m:repr[L],ri: repr[Ri], ro: repr[Ro]): Fundef1[(L, Ri), (L, Ro)] =  {
      val param = pL[L, Ri]("p" + l.shortName) //parameter names inform about locus
      Fundef1(unopfunName(o, l)(ri,ro), unop[L,Ri,Ro](o, param), param) // we compute a function of one argument. res is the body, param are the single parameter
    }

    /**

     * @return function in scala which does the corresponding unary operatrion,  memoised in unopmem
     */
    def getUnopFun[L<:Locus, Ri <: Ring,Ro<:Ring](o:Fundef1[Ri,Ro], l: L)(implicit m:repr[L],ri: repr[Ri], ro: repr[Ro]):  Fundef1[(L, Ri), (L, Ro)]  = {
      val funName = unopfunName(o, l)(ri,ro)
      if (!unopmem.contains(funName)) //redSmem memoizes so that we 'd compile the function only once.
        unopmem = unopmem + (funName -> unopfunDef(o, l)(m,ri,ro))
      unopmem(funName).asInstanceOf[  Fundef1[(L, Ri), (L, Ro)]]
    }


  }

}
