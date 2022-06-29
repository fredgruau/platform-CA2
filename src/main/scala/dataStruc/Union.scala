package dataStruc

import compiler.Instr
import dataStruc.Align._

import scala.collection.{Iterable, immutable, mutable}

object Union {
  /** @toSort List of DagNodes  extending union so that we can access their root
   * @return regroup in distincts iterable,  elements of toSort having identical root */
  def paquetsOld[T <: Union[T]](toSort: List[T]): immutable.Iterable[Iterable[T]] = {
    val m = mutable.LinkedHashMap.empty ++ toSort.map(x => x -> x.root) //computes a map associating each element its root
    m.groupBy(_._2).map { case (_, v) => v.keys }
  }

  def paquets[T <: Union[T]](toSort: List[T]) = indexedPaquets(toSort).values

  /** builds a map associating for each root, the list of its component's element */
  def indexedPaquets[T <: Union[T]](toSort: List[T]): Map[T, List[T]] = toSort.groupBy(_.root)

}

trait Union[T <: Union[T]] {
  self: T =>
  protected var parent: T = this

  def reset = {
    parent = this
  }

  private var rank = 0

  def aligned = false;


  def root: T = if (parent == this) parent else {
    parent = parent.root; parent
  } // "compressing path towards the root."
  /** to be defined if we need to compute alignement
   *
   * @param xroot former root,
   * @param x     element which need to be aligned on
   * @param y     new element to be aligned to */
  def transitiveClosure(xroot: T, x: T, y: T): Unit = {}

  /** There will be some check to do on align two instruction already sharing roots are merged */
  def checkIsSameRoot(x: T, y: T): Unit = {}

  def union(y: T, doAlign: Boolean = true): Unit = {
    val xroot = root;
    val yroot = y.root
    if (xroot != yroot) { //dans le cas de align, si xroot = yroot faut quand meme vérifier que les alignement coincide.
      if (xroot.rank < yroot.rank) {
        if (doAlign) transitiveClosure(xroot, this, y); //x was aligned to x root, now it must be aligne to y's root
        xroot.parent = yroot; //the parent of x directly points to the new root
      }
      else {
        yroot.parent = xroot;
        if (doAlign) transitiveClosure(yroot, y, this)
        if (xroot.rank == yroot.rank) xroot.rank += 1
      }
    }
    else (checkIsSameRoot(this, y)) //x and y are already in the same component. we must check if alignement coincide
  }
}
