package progOfCA

import compiler.SpatialType._
import compiler.AST._
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.hexagon
import compiler._
import progOfCA.Rand.randDef
import compiler.SpatialType._
/** Layer implementing a random bit */
class Rand() extends Layer[(V, B)](1, "rand") with ASTLt[V, B] {
  val next: BoolV = new Call1(randDef, this) with BoolV //randDef is used only here, no need for a wrapper!
  show(this)
}

object Rand extends App {
  /** macro computing the next state of a random bit */
  private[Rand] val randDef: Fundef1[(V, B), (V, B)] = {
    val b = pL[V, B]("blob")
    val nasI: UintV = concatR(transfer(v(orR(transfer(e(b))))))
    nasI.setName("neighborasInt");
    val (n0, n1, n2, n3, n4, n5) = (elt(0, nasI), elt(1, nasI), elt(2, nasI), elt(3, nasI), elt(4, nasI), elt(5, nasI))
    //val randBit=xorn(orn(n0,n1,n2),n3,n4,n5)
    val randBit: ASTLt[V, B] = (n0 | n1 | n2) ^ n3 ^ n4 ^ n5
    randBit.setName("randBit");
    Fundef1("rand", randBit, b)
  }


  new Circuit[V, B]() {
    val rand = new Rand();

    def computeRoot: BoolV = rand
  }.compile(hexagon)


}

