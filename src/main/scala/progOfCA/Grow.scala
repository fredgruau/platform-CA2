/*
package progOfCA /** contains variation of grow starting with basic growth,
  and then growth to voronoi cells , illustrate redS sytematic computation*/

import compiler.ASTLfun.{neighbors, v}
import compiler.AST.{Layer, delayed, pL}
import compiler.ASTBfun.orRedop
import compiler.SpatialType.{BoolE, _}
import compiler.ASTL._
import compiler.Circuit.hexagon
import compiler.{AST, ASTBfun, ASTLt, B, Circuit, E, F, T, UI, V, repr}
import progOfmacros.Wrapper.{borderS, existS, insideS, transferMacro}
import compiler.ASTLfun._
import compiler.ASTLt.ConstLayer
import compiler.repr.nomE
import dataStruc.{BranchNamed, Named}
import progOfmacros.Topo.brdin
import sdn.Util.{addBlobE, addBlobVe, newaddBlobVe, safeGrow}
import sdn.{Blob, BlobE, BlobV, Compar, Compar3}
/** same as GrowVorV but based on a boolVe support  MARCHE PAS*/
class Grow() extends Layer[(V, B)](1, "global") with BoolV  with BranchNamed {
  val is:BoolV=delayedL(this)
  val edge: ASTLt[E, B] =borderS(is)
  val brd=brdin(edge,is)
  val blb=addBlobVe( brd,edge)
  override val next: AST[(V, B)] = this | safeGrow(blb)  //we extend the blob around the border brdV, except for meeting points
  show(is,blb.meetE,brd)
}
/** test growVorV/E/Ve by wrapping in a useless constant layer */
class GrowTest()  extends ConstLayer[V, B](1, "global")  with BranchNamed{
  //  val g=new GrowVorVTest();show(g,g.meetE,g.meetV)
  val g=new Growtt(); // brd,emptyRhomb1, emptyRhomb,twoAdjBlob,
  //val g=new GrowVorVeTest();show(g,g.ve.meetE,g.ve.meetV) // brd,emptyRhomb1, emptyRhomb,twoAdjBlob,
  show(g, g.next, g.n, g.brd)
}

/** Simple growth from V to E to V; test of in, and bordern
 * it uses transfer as a macro.
 * we believe that at least for border, and neighbor, it will be reused */
class Growtt extends Layer[(V, B)](1, "global") with ASTLt[V, B] with BranchNamed{
  val broadcasted:BoolVe = broadcast(this )//step 1 is broadcast
  val transfered :BoolEv= transferMacro(broadcasted) //step 2 is transfer
  val n2 = reduce(orRedop[B], transfered) //(n,m,d) yzeté implicit killerest
  val n: BoolE = existS(this);
  // val in: BoolE = inside(this);
  val brd: BoolE = borderS(this);
  override val next: BoolV = existS(n2) //   uses  defVe implicitely, the override keyword is mandatory

  // he name of root to arg(0).lowercase
}
/** Simple growth from V to E to V; test of in, and border.we believe that at least for border, and neighbor, it will be reused */
class GrowRaw extends Layer[(V, B)](1, "global") with ASTLt[V, B] with BranchNamed{
  val n: BoolE = existS(this);
  // val in: BoolE = inside(this);
  val brd: BoolE = borderS(this);
  override val next: BoolV = existS(n) //   uses  defVe implicitely, the override keyword is mandatory

  // he name of root to arg(0).lowercase
}

/** test growVorV/E/Ve by wrapping in a useless constant layer */
/*class GrowVorTestOld()  extends ConstLayer[V, B](1, "global")  with BranchNamed{
  //  val g=new GrowVorVTest();show(g,g.meetE,g.meetV)
  //val g=new GrowVorETest();
  val g=new GrowVorVeTest();
  show(g,g.blb.meetE,g.blb.meetV) // brd,emptyRhomb1, emptyRhomb,twoAdjBlob,
  //val g=new GrowVorVeTest();show(g,g.ve.meetE,g.ve.meetV) // brd,emptyRhomb1, emptyRhomb,twoAdjBlob,
}*/
/** uses plain  blobV computation to grow seed into Voronoi region, just by stoping the growth just before merge happens */
class GrowVorVTest() extends Layer[(V, B)](1, "global") with BoolV with BlobV with BranchNamed {
  override val next: AST[(V, B)] = this | safeGrow(this) //we extend the blob around the border brdV, except for meeting meeting points
  //show(b.meet) // brd,emptyRhomb1, emptyRhomb,twoAdjBlob,
}

/** same as GrowVorV but based on a boolE support  */
class GrowVorETest() extends Layer[(V, B)](1, "global") with BoolV  with BranchNamed {
  val is:BoolV=delayedL(this)
  val blb: Blob =addBlobE(borderS(is))  //for a correct testing, edge should be an arbitrary line,
                                          // and not the border of a boolV
  /** we directly build an instance of HasBrdE from the edge, */
  override val next: AST[(V, B)] = this | safeGrow(blb) //we extend the blob around the border brdV, except for meeting meeting points
}





/*
/** Simple growth using directly the neighbor vertice,  that is a bit cheaper */
class GrowN extends Layer[(V, B)](1, "global") with ASTLt[V, B] {
  override val next: BoolV = orR(neighbors(this)) //  make use of defVe brough to us implicitely,
  // nb if overrid is not written, it does not work!
  show(this) //shown field will get the name "grow", because we set the name of root to arg(0).lowercase
  show(next)
}

/** Growing by passing through from V through F */
class GrowF extends Layer[(V, B)](1, "global") with ASTLt[V, B] {
  val nf: BoolF = existS(this); //no use of  defEv
  override val next: BoolV = existS(nf) //  make use of defVf brough to us implicitely,nb if overrid is not written, it does not work!
  show(this, nf, next)

}

/** Growing  from E through F */
class GrowEF extends Layer[(E, B)](1, "global") with ASTLt[E, B] {
  val broadcasted = f(this) //step 1 is broadcast
  val transfered = transfer(broadcasted) //step 2 is transfer
  val nf = orR(transfered) //(n,m,d) yzeté implicit killerest
  override val next: BoolE = existS(nf) //  make use of defVe brough to us implicitely,nb if overrid is not written, it does not work!
  show(this, broadcasted, transfered, nf, next)
}

/** Growing  from E through V */
class GrowEV extends Layer[(E, B)](1, "global") with ASTLt[E, B] {
  val broadcasted = v(this) //step 1 is broadcast
  val transfered = transfer(broadcasted) //step 2 is transfer
  val nv: BoolV = orR(transfered) //(n,m,d) yzeté implicit killerest
  override val next: BoolE = existS(nv) //  make use of defVe brough to us implicitely,nb if overrid is not written, it does not work!
  show(this, broadcasted, transfered, nv, next)
}*/









*/
