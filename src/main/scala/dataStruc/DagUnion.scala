package dataStruc

import scala.collection.Iterable

/**
 * Dag whose node have the additional ability to define connected components.
 */

trait DagUnion[T <: DagNode[T] with Union[T]] extends Dag[T] {
  self: Dag[T] =>
  /**
   *
   * @param p predicates defining adjacence
   * @return connected components, as Iterable Sequence
   */
  def components(p: (T, T) => Boolean): Iterable[Iterable[T]] = {
    for (src <- visitedL)
      for (target <- src.inputNeighbors)
        if (p(src, target)) {
          //          if(target.isShift)
          //            {val name=target.names(0).drop(5)
          //            if(src.names(0)==name)
          //              println("toto")}
          src.union(target)
        }
    Union.paquets(visitedL)
  }
}

