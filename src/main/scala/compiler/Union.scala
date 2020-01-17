package compiler

import compiler.Align._

trait Union2[T] {
  private var parent: Union2[T] = this
  def root: Union2[T] = if (parent == this) parent else { parent = parent.root; parent } // "compressing path towards the root."

}
trait Union[T<:Union[T]] {   self:T =>
  private var rank = 0
  protected var parent: T = this
  protected var xroot, yroot = null
  def root: T = if (parent == this) parent else { parent = parent.root; parent } // "compressing path towards the root."
  /**to be defined if we need to compute the transitive closure.  */
  def transitiveClosure (xroot: T, x:T, y: T) = {}
  def union (y: T) = {
    val xroot = root; val yroot = y.root
    if (xroot != yroot) { //dans le cas de align, si xroot = yroot faut quand meme vérifier que les alignement coincide. 
      if (xroot.rank < yroot.rank) { transitiveClosure(xroot,this , y); xroot.parent = yroot;  }
      else {
        yroot.parent = xroot; transitiveClosure(yroot,y, this)
        if (xroot.rank == yroot.rank) xroot.rank += 1
      }
    }
  }
}



/** adds the possiblity  to compute an alignement to the root, while computing the root*/
trait Align[T<:Align[T]] extends Union[T] { self:T =>
  def neighborAlign(n:T): Array[Int]
  /**permutation to apply in order to go from this to parent! */
  private var alignToPar: Array[Int] = Array.range(0, 6) //  neutral permutation
  def alignToRoot: Array[Int] = if (parent == this)  Array.range(0, 6) else compose(alignToPar, parent.alignToRoot)
  override def root: T = if (parent == this) this else { alignToPar = alignToRoot; parent = parent.root;   parent } // "compressing path towards the root."
  override def transitiveClosure (xroot : T,x : T, y: T)  ={
    val ny=x.neighborAlign(y); xroot.alignToPar=if(y==null) null else compose(invert(x.alignToRoot), compose(ny, y.alignToRoot))
  }
 }

object Align {
 /** Computes T2 o T1 */
  def compose(T1: Array[Int], T2: Array[Int]): Array[Int] = {
    if(T1==null||T2==null) return null 
    val r =   new Array[Int](6)
    for (i <- 0 to 5) r(i) = T2(T1(i))
    r
  }
  def hcompose(T1: Array[Int], T2: Array[Int]): Array[Int] = {
    if(T1==null||T2==null) throw new RuntimeException("nullarray")
      return compose(T1,T2) 
  }

  def invert(T: Array[Int]): Array[Int] = {
    val r =  new Array[Int](6)
    for (i <- 0 to 5) r(T(i)) = i
    r
  }
}