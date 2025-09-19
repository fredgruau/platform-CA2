package progOfLayer

//used to test quick voronoisation protocol, realized throug a locus proximity graph precomputed for a small CA
//a singe java is generated, so we can use if for compiling java directly;
import compiler.AST.Layer
import compiler.ASTL.{clock, transfer}
import compiler.ASTLfun.orR
import compiler.SpatialType._
import compiler._
import dataStruc.BranchNamed
/** we test the display using a TVe constant layers, initialized randomly*/
class Testvoronoi() extends Layer[(T[V,E],B)](1,"global")  with BoolVe with BranchNamed{
  //l'init de Ve ne marche pas parfaitement a cause du preparebit, on s'en fout.
/*val Ev:BoolEv=transfer(this)
/l V:BoolV=orR(this)
val E:BoolE=orR(Ev)
val Vf:BoolVf=clock(this)
val Fv=transfer(Vf)
val F:BoolF=orR(Fv)
val Ef:BoolEf=clock(Ev)
val Fe=transfer(Ef)*/
  import ASTLfun.fromBool
  val testConst:BoolVe=true
  val otherUse=testConst ^ this
  /** the value at t, is the strate itself. */
override val next= this
  show(this,testConst,otherUse)
//show(Ev,E,V,Fv,Vf,F,Ef,Fe)

}


