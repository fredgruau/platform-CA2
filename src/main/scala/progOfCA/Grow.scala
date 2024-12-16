package progOfCA //contains variation of grow, illustgrate redS sytematic computation
 //contains lots of different way of growing, and in particular, growing to voronoi cells
import compiler.ASTLfun.{neighbors, v}
import compiler.AST.{Layer, delayed, pL}
import compiler.SpatialType.{BoolE, _}
import compiler.ASTL._
import compiler.Circuit.hexagon
import compiler.{AST, ASTBfun, ASTLt, B, Circuit, E, F, T, UI, V}
import progOfmacros.Wrapper.{borderS, existS, insideS}
import compiler.ASTLfun._
import compiler.ASTLt.ConstLayer
import compiler.repr.nomE
import dataStruc.{BranchNamed, Named}
import progOfmacros.Topo.brdin
import sdn.Util.{addBlobE, addBlobVe, safeGrow}
import sdn.{BlobE, BlobV, Compar, Compar3, ComparApex}


/** test growVorV/E/Ve by wrapping in a useless constant layer */
class GrowVorTest()  extends ConstLayer[V, B](1, "global")  with BranchNamed{
  //  val g=new GrowVorVTest();show(g,g.meetE,g.meetV)
  val g=new GrowVorETest();show(g,g.edge.meetE,g.edge.meetV) // brd,emptyRhomb1, emptyRhomb,twoAdjBlob,
  //val g=new GrowVorVeTest();show(g,g.ve.meetE,g.ve.meetV) // brd,emptyRhomb1, emptyRhomb,twoAdjBlob,
}


/** uses plain  blobV computation to grow seed into Voronoi region, just by stoping the growth just before merge happens */
class GrowVorVTest() extends Layer[(V, B)](1, "global") with BoolV with BlobV with BranchNamed {
  override val next: AST[(V, B)] = this | safeGrow(this) //we extend the blob around the border brdV, except for meeting meeting points
  //show(b.meet) // brd,emptyRhomb1, emptyRhomb,twoAdjBlob,
}

/** same as GrowVorV but based on a boolE support  */
class GrowVorETest() extends Layer[(V, B)](1, "global") with BoolV  with BranchNamed {
  val is:BoolV=delayedL(this)
  val edge=addBlobE(borderS(is))  //for a correct testing, edge should be an arbitrary line, and not the border of a boolV
  /** we directly build an instance of HasBrdE from the edge, */
  override val next: AST[(V, B)] = this | safeGrow(edge) //we extend the blob around the border brdV, except for meeting meeting points
}

/** same as GrowVorV but based on a boolVe support  */
class GrowVorVeTest() extends Layer[(V, B)](1, "global") with BoolV  with BranchNamed {
  val is:BoolV=delayedL(this)
  val edge: ASTLt[E, B] =borderS(is)
  val ve=addBlobVe( brdin(edge,is))
   override val next: AST[(V, B)] = this | safeGrow(ve)  //we extend the blob around the border brdV, except for meeting meeting points
}



/*
/** Simple growth from V to E to V; test of in, and border.we believe that at least for border, and neighbor, it will be reused */
class Grow extends Layer[(V, B)](1, "global") with ASTLt[V, B] {
  val n: BoolE = existS(this);
  // val in: BoolE = inside(this);
  val brd: BoolE = borderS(this);
  override val next: BoolV = existS(n) //   uses  defVe implicitely, the override keyword is mandatory
  show(this, next, n, brd)
  // he name of root to arg(0).lowercase
}

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









