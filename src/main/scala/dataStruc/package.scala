import java.awt.print.Printable

import compiler.Instr

import scala.collection.{Iterable, Map}
import scala.collection.immutable.HashSet

package object dataStruc {
  def toSet[T](a: Iterable[T]): HashSet[T] = HashSet() ++ a

  def toSet[T](a: List[T]): HashSet[T] = HashSet() ++ a

  def overlap[T](a: Iterable[T], g: HashSet[T]): Boolean = {
    !toSet(a).intersect(g).isEmpty
  }

  /** Used to store alignement to root, as well as schedule */
  type Schedule = Map[String, Array[Int]]

  def id6: Array[Int] = Array(0, 1, 2, 3, 4, 5)

  def isIdentity(t: Array[Int]): Boolean = t != null && (t sameElements id6)


}
