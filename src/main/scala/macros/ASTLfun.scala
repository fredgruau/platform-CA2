package macros

//import compiler._
import compiler.AST._
import compiler.ASTL._
import compiler.ASTB._
import compiler.{ASTLt, B, E, Locus, Ring, SI, T, UI, V, repr}

/** Contains the code of locus function used as a layer of  building blocks of small bits of spatial operators, compiled with optimal perf. */
object ASTLfun {

  // @TODO we should not import compiler._, and find a way to use parameter with IntV rather than [V,SI]
  def p[L <: Locus, R <: Ring](name: String)(implicit n: repr[L], m: repr[R]) = new Param[(L, R)](name) with ASTLt[L, R]
  /**From an IntV, computes the gradient sign, and the delta to be added to make it a distance  */

  val slopeDeltaDef: Fundef1[(V, SI), ((T[E, V], B), (V, SI))] = {
    //val x:IntV= p[V, SI]("dis")
    val x = p[V, SI]("dis")
    val tepred = transfer(e(x))
    val g=subESI(tepred)
    val grad:IntvE = sendv(List(g,-g))
  //  val grad: IntvE = tepred - sym(tepred) //TODO should use opp to make only one subtraction, we need to adress selectively the two neighbors of an edge.
    val slope: BoolvE = gt(grad)
    val tslope=transfer(slope)
    val delta: IntV = minR(transfer(sign(grad + -2)))
    //val temp: BoolfV = xorR2(tslope )
    val temp: BoolfV =   clock(~tslope)
    val temp2: BoolfV =   anticlock(~tslope)
    //val temp6:BooleV= sym( tslope)
    //val temp5:BoolfV=clock(~temp6)
  //  val temp3: BoolfV =  or( temp5,xor( temp, temp2))
    val vortex: BoolF =  orR(transfer(xor( temp, temp2)))
   // val test= vortex |   andR(transfer(temp5)) ;  slope.bugif(test) //ceci provoque bien l'erreur attendue java.lang.RuntimeException: Debug exp is allzero=>not usable for compute
                                                 //ca montre que debug ne peut etre réutilisé.
    slope.bugif(vortex) //rajoute l'instruction bugif dans la liste des instructions de slope.
    grad.setName("grad"); tepred.setName("tepred"); slope.setName("slope"); delta.setName("delta"); vortex.setName("vortex")
    Fundef1("boolgrad", Coons(slope, delta), x)
  }

  /**Calls boolgrad, and separate the two results.  */
  def slopeDelta(d: IntV): (BoolvE, IntV) = { val r = Call1(slopeDeltaDef, d); (new Heead(r) with BoolvE, new Taail(r) with IntV) }

}