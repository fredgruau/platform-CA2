package progOfCA

import compiler.AST._
import compiler.SpatialType.{BoolVe, _}
import compiler.ASTBfun.{addRedop, andRedop, minSignRedop, orRedop, p, redop, xorRedop}
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.ASTLt._
import compiler.Circuit.hexagon
import compiler._
import compiler.SpatialType._
import dataStruc.BranchNamed
import progOfmacros.Grad
import progOfmacros.Wrapper.borderS
import progOfmacros.RedT.cacOld
import sdn.BlobOld
import sdn.Util.addBlobVe


class Dist(val source: Layer[(V, B)]/*should be a strate here*/,val bitSize:Int) extends Layer[(V, SI)](bitSize, "0") with ASTLt[V, SI] with BranchNamed{
  val opp = -this
  val (sloplt: BoolVe, delta, level, gap) = Grad.slopDelta(this) //faudrait que je récupére la date du fichier ou se trouve slopeDelta
  //gabriel centers can be directly obtain simply by taking meeting point of the blob, using sloplt
  //however, when computing E meeting point there is a difficulty due to the fact that the orientation matters.
  //val b = new BlobOld(orR(transfer(sloplt)), sloplt, orR2(sloplt))
  val b = addBlobVe(sloplt)

  //when computing brdE, we need it to be either true or false on the border
  // we can decide to set it to true only if there is a blob, or allways, in which case there will be a center all around the chip,
  // which may be appropriate if we want ports all around the chip. If we want this last behavoir
  // we need to use OR2 instead of OR, where neutral will
  // true instead of false.
  show(b.meetE, b.meetV)
  //the idea here is to compute all what is neccessary from the gradient, so that we do not need to store the gradient which would be heavey
  //val topoligne: BoolE = border(elt(2, this)); //allows to visualize the field by coloring edges instead of  vertices
  val vortex: BoolF = andR(transfer(cacOld(xorRedop[B]._1, sloplt))) // andR( transfer(clock(sloplt) ^ anticlock(sloplt))); //transitive circular lt

  //  bugif(vortex) //rajoute l'instruction bugif dans la liste des instructions de slope.
  show(level, vortex, gap,sloplt, delta) // topoligne, //,
  val next: ASTLt[V, SI] = this + cond(source.asInstanceOf[BoolV], sign(opp), delta) //faudrait en faire une macro qui prends delta, source et dist et renvoie distNext

}

trait DistT {
  self: Layer[(V, B)] => //adds a distance to a LayerV todo, it should also limit its movement
  val d = new Dist(self,5);
  //show(d); les show doivent etre fait dans le main
}


/** contains show(dist) otherwise, class Dist is not compiled at all, because not used from the root */
trait DistSimplerT {
  self: Layer[(V, B)] => //adds a distance to a LayerV todo, it should also limit its movement
  val dist = new DistSimpler(self);
 // show(dist); les show doivent etre fait dans le main

}

/** a simpler version of distance, which does not uses send */
class DistSimpler(val source: Layer[(V, B)]) extends Layer[(V, SI)](3, "0") with ASTLt[V, SI] {
  /*val level: BoolV = elem(2, this);*/
  val grad: IntVe = neighbors(this) - e(this)
  val lt: BoolVe = ltSI(grad)
  val eq: BoolE = ~reduce[E, V, B](orRedop[B], transfer(lt)) //its equal if it is neither lt nor gt
  val delta: IntV = reduce(minSignRedop, sign(extend(4, grad) + 2)) //we need to add 2, using one more bit, in order to add modulo 16 and not 8
  val next: ASTLt[V, SI] = this + cond(source.asInstanceOf[BoolV], sign(-this), delta) //faudrait en faire une macro qui prends delta, source et dist et renvoie distNext
  show(lt, eq)
}

