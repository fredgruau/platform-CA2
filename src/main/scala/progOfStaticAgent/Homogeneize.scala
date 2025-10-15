package progOfStaticAgent

import compiler.ASTL.{ASTLg, anticlock, clock, delayedL, sym, transfer}
import compiler.ASTLfun.{cond, e, imply}
import compiler.SpatialType.{BoolV, BoolVe, BoolVf}
import compiler.{AST, ASTBfun, ASTLt, B, E, Locus, Ring, SI, T, V, chip}
import dataStruc.{BranchNamed, Named}
import progOfmacros.Comm.{adjacentBall, insideBall, neighborsSym}
import progOfmacros.RedT.cac
import progOfmacros.Wrapper
import progOfmacros.Wrapper.{border, borderS, exist, existS, inside, insideS, smoothen, smoothen2, testShrink}
import sdn.MuStruct.showMustruct
import sdn._
import sdntool.{addDist, addDistGcenter}

/**illustrate the working of repulsion combined with exploration  */
class Homogeneize() extends LDAG with Named with BranchNamed
{ val part=new Convergent()
  //val part=new Homogen()
  part.showMe
  part.bf.showMe
  part.b.showMe
  part.gc.showMe
  part.d.showMe; part.dg.showMe
  part.sf.showMe
  showMustruct
}

/** basic quasiparticle with blob and qpoint constraints */
class Seed extends  MovableAgentV  with addBloobV with blobConstrain with addQpointFields with QpointConstrain

/** moves as much as possible */
class Flies2 extends Seed {
  /** exploring priority */  final val explore=introduceNewPriority()
  force(explore, "explore",'O', Force.total)
  //final val explore2=introduceNewPriority() // force(explore2, "toto",'P', Force.total)
}

/**adds distance, gabriel center,  distance to gabriel center, and then finally repulsive force*/
class Homogen() extends Flies2 with addDist with addGcenter with addDistGcenter
{  /** homogeneizing priority */
  final val homogeneize=introduceNewPriority()
  force(homogeneize,"repulse",'|',dg.repulse)//specific forces applied to Flies
  shoowText(dg.muis, List())

  //showMoves
};

class Convergent extends Homogen // with Lead //pas besoin de leader pour le moment
{  val sf=new Attributs() { //sf==stableFields
  override val muis: ASTLg with carrySysInstr = Convergent.this.muis
  /** border of qparticle  where dg diminishes */
  val brdVeSloped=bf.brdVe & dg.sloplt
  /** around isV, adds Vertices on the otherside of brdVeslopped */
  val isVplus=isV | exist(transfer(sym(transfer(brdVeSloped))))
  /** add vertex  if three neighbors are on */
  val isVsmoothed=smoothen(isVplus)
  /** computes the Vf bool and yes that is right*/
  val isVtest=testShrink(isVplus)
  /** add vertex  if four neighbors are on, bugs, more restrictive therefore, than smoothen */
  val isVsmoothed2: BoolV =isVplus| exist(isVtest)
  // shoow(isVplus,isVsmoothed,isVsmoothed2,isVtest)  /** true for one seed if on its whole border dg diminishes */
  //val stable1Old=muis & inside(imply(brdVe,dg.sloplt))
  val stable1=Convergent.this.muis.asInstanceOf[BoolV] & insideBall(isVsmoothed2)
  val stable2=forallize(stable1) & isV

  override def showMe: Unit =  shoow(stable1,stable2)
}
  val stabilize=introduceNewPriority()
  val balance: Force = new Force() {
    import compiler.ASTLfun.fromBool
    override def actionV(ag: MovableAgentV): MoveC = {
      /** pure negative move */
      val yes=MoveC1(false,false)
      /** if stable2 , this will cancel movement of lower priority, */
      val no = MoveC1(sf.stable2, e(sf.stable2)& bf.brdVe)
      MoveC2(yes,no)
    }
  }
  force(stabilize,"balance",'_',balance)//specific forces applied to Flies

}

/**
 *
 * @param source quasiparticle
 * identifies a vertex within source, may be not usefull after all,
 * since it is arguably easier to compute stuf on the whole particle support*/
class Leader(source: Seed)extends MuStruct [V,B] {
  override def inputNeighbors: List[MuStruct[_ <: Locus, _ <: Ring]] = List(source)

  /** should be initialized globally,  exactly as source */
  val sourceNext = source.muis.next.asInstanceOf[BoolV]
  /** true if leader is no longer on the support of its source */
  val sourceOfLeaserHasMoved = source.isV & ~sourceNext & delayedL( muis.pred)
  /** extends sourceHasMoved to the adjacent Vertices */
  val sourceMovedWide = adjacentBall(sourceOfLeaserHasMoved)

  val neighborSourceNext: BoolVe = transfer(sym(transfer(e(sourceNext))) ) & e(delayedL( muis.pred))
  /** by hypothesis, neighborSourceNext is a segment, electedNeigbor is just the first element of this segment */
  val electedNeigbor1: BoolVf = cac(ASTBfun.delta, neighborSourceNext)
  val electedNeigbor2: BoolVe=anticlock(electedNeigbor1)
  val elected3: BoolV =  exist(transfer(sym(transfer(electedNeigbor2))))
  override val muis: LayerS[V, B] = new LayerS[V, B](1, "global") {
    /** we have to consider sym to finally retrieve the new leader. */
      override val next: AST[(V, B)] = delayedL(cond(sourceMovedWide,elected3,this.pred))(this.mym)
  }

  shoow(electedNeigbor2,electedNeigbor1,sourceMovedWide,neighborSourceNext,elected3)

  import compiler.ASTLfun.fromBool //pour avoir la conversion implicite de boolean vers boolVe
 /** annule le mouvement si stable, donc seul no est défini */
  val balance: Force = new Force() {
    override def actionV(ag: MovableAgentV): MoveC = {
      val yes=MoveC1(false,false) //convergent is a pure negative move
      val no = MoveC1(muis, false) //ne va pas empty sur leader, juste pour tester
    MoveC2(yes,no)
    }
  }
}
trait Lead {
  self: Seed => //adds a leader to seed ,
  val myleader=new Leader(this);
  //show(d); les show doivent etre fait dans le main
}