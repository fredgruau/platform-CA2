package progOfCA
//used to test quick voronoisation protocol, realized throug a locus proximity graph precomputed for a small CA
//a singe java is generated, so we can use if for compiling java directly;
import compiler.AST.Layer
import compiler.ASTL.{clock, transfer}
import compiler.ASTLfun.{orR, toNeighb}
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.{BoolE, BoolEf, BoolEv, BoolF, BoolV, BoolVe, BoolVf}
import compiler._
import progOfCA.Force.qpointRand
import progOfmacros.RedSwrapper.exist

import java.util
/** we test the display using a TVe constant layers, initialized randomly*/
class Testvoronoi() extends Layer[(T[V,E],B)](1,"global")  with BoolVe{
  val Ev:BoolEv=transfer(this)
  val V:BoolV=orR(this)
  val E:BoolE=orR(Ev)
  val Vf:BoolVf=clock(this)
  val Fv=transfer(Vf)
  val F:BoolF=orR(Fv)
  val Ef:BoolEf=clock(Ev)
  val Fe=transfer(Ef)
  /** the value at t, is the strate itself. */
  override val next= this
  show(Ev,this,E,V,Fv,Vf,F,Ef,Fe)

}


