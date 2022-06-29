package dataStruc

import compiler.Instr

object Align {
  /** Computes T2 o T1 */
  def compose(T1: Seq[Int], T2: Seq[Int]): Array[Int] = // T1.map(T2(_))
  {
    if (T1 == null || T2 == null) return null
    val taille = math.min(T1.length, T2.length)
    val r = new Array[Int](taille)
    for (i <- 0 to taille - 1) r(i) = T2(T1(i))
    r
  }

  def compose2(T1: Seq[Int], T2: Seq[Instr]): Array[Instr] = // T1.map(T2(_))
  {
    if (T1 == null || T2 == null) return null
    val r = new Array[Instr](6)
    for (i <- 0 to T1.length - 1) r(i) = T2(T1(i))
    r
  }

  def compose3[A](T1: Seq[Int], T2: Array[A]): Array[A] = // le bon
  {
    if (T1 == null || T2 == null) return null
    val r = T2.clone()
    for (i <- 0 to T1.length - 1) r(i) = T2(T1(i))
    r
  }


  //def antecedant(T1: Seq[Int], T2: Seq[Int])
  def isPermutation(t: Array[Int]): Boolean = {
    val l = t.toList.sortWith(_ < _)
    return l == List(0, 1, 2, 3, 4, 5);
  }

  /* def invert(t: Array[Int]): Array[Int] = {
     //assert(isPermutation(t))
     val r =  new Array[Int](t.length)
     for (i <- 0 to t.length-1) r(t(i)) = i
     r
   }*/
  def invert(t: Seq[Int]): Array[Int] = {
    //assert(isPermutation(t))
    val r = new Array[Int](t.length)
    for (i <- 0 to t.length - 1) r(t(i)) = i
    r
  }
}

import Align._

/** adds the possiblity  to compute an alignement to the root, while computing the root of a union */
trait Align[T <: Align[T]] extends Union[T] {
  self: T =>
  /** implements alignement with respect to neighbor */
  def neighborAlign(n: T): Array[Int]

  /** permutation to apply in order to go from this to parent! */
  private var alignToPar: Array[Int] = Array.range(0, 6) //  neutral permutation
  /**
   * will compute alignement
   */
  override def reset = {
    super.reset;
    alignToPar = Array.range(0, 6)
  }

  /** @return aligntoRoot(shedule) = rootschedule */
  def alignToRoot: Array[Int] =
    if (parent == this)
      Array.range(0, 6)
    else Align.compose(alignToPar, parent.alignToRoot)

  override def root: T = if (parent == this) this else {
    alignToPar = alignToRoot;
    parent = parent.root;
    parent
  } // "compressing path towards the root."
  /** to be defined if we need to compute alignement
   *
   * @param xroot former root of x,
   * @param x     element which need to be aligned on
   * @param y     element whose root is the new root */
  override def transitiveClosure(xroot: T, x: T, y: T): Unit = {
    val ny = x.neighborAlign(y); //align from x to y
    xroot.alignToPar =
      if (y == null) null
      else if (x.alignToRoot == null) null //rajouté récemment pour éviter des plantages sauvages
      else compose(invert(x.alignToRoot), compose(ny, y.alignToRoot)) //align from xroot to y's root is
    //equal to alig from xroot to x (we must take the invert of alignto root)
    //commposed with align from x to y composed with align from y to y's root.
  }

  /** gives an error message to investigate if a cycle is to be installed */
  override def checkIsSameRoot(x: T, y: T): Unit = {
    if (aligned)
      if (x.alignToRoot.toList != y.alignToRoot.toList) //TODO we must compose with the alignement from x to y!!
      throw new RuntimeException("instructions mis-aligned, needs a cycle" + x.alignToRoot.toList + y.alignToRoot.toList)
  }

}

