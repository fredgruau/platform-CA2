import compiler.Instr

import scala.collection.Iterable
import scala.collection.immutable.HashSet

package object dataStruc {
  def toSet[T](a: Iterable[T]): HashSet[T] = HashSet() ++ a

  def toSet[T](a: List[T]): HashSet[T] = HashSet() ++ a

  def overlap[T](a: Iterable[T], g: HashSet[T]): Boolean = {
    !toSet(a).intersect(g).isEmpty
  }

}
