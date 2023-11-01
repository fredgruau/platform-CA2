package dataStruc

import compiler.Circuit.{iTabSymb, iTabSymb2}
import dataStruc.Align2.compose

import java.io.{BufferedWriter, File, FileWriter}
import java.util.regex.Pattern
import scala.collection.immutable.HashMap
import scala.collection.{Map, Seq, mutable}
import scala.reflect.ClassTag


object Util {

  def writeFile(filename: String, s: String): Unit = {
    val file = new File(filename)
    val bw = new BufferedWriter(new FileWriter(file))
    bw.write(s)
    bw.close()
  }

  def append2File(filePath: String, s: String): Unit = {
    import java.nio.file.Files
    import java.nio.file.Paths
    val former = new String(Files.readAllBytes(Paths.get(filePath)))
    val file = new File(filePath)
    val bw = new BufferedWriter(new FileWriter(file))
    bw.write(former.dropRight(1) + "\n" + s + "}") //we remove the former parenthesis, which has to be the last char,  and add a new one
    bw.close()
  }

  /**
   *
   * @param displayed a list of displayed fiedl,
   * @return relation fatherToSon  where father is a string, sons is a list of strings
   */
  def hierarchyDisplayedField(displayed: Set[String]): Map[String, Set[String]] = {
    var res: Map[String, Set[String]] = new HashMap()

    /**
     *
     * @param father
     * @param son
     * adds on to the list of sons of father
     */
    def addSon(father: String, son: String): Unit =
      if (res.contains(father)) //father has already been spoted
        res = res + (father -> (res(father) + son))
      else res = res + (father -> Set(son)) //father is spoted for the first time

    def addPath(str: String): Unit = {
      val f: String = fatherOfVar(str)
      if (f.nonEmpty) {
        addSon(f, str)
        addPath(f)
        // if (displayed.contains(f))
        //  addSon(f, f + lastPathPart(f)) //if a layer is displayed, we must add itself as a field so that it will be printed
        // it is both a layer and a field
      }
    }

    for (v: String <- displayed)
      addPath(v)
    res
  }

  /**
   *
   * @param root       internal node on which to start
   * @param father2son relates a father to its list of sons, within  chain caracterizing path to displayed fields.
   * @return a parenthesized expression encoding the subtree starting at "root". */
  def parenthesizedExp(root: String, father2son: Map[String, Set[String]]): String = {
    if (!father2son.contains(root)) return root //"(" + root + ")"
    val sons = father2son(root)
    root + "(" + sons.map(parenthesizedExp(_, father2son)).mkString(")(") + ")" // + "." //the point is necessaru when the tree is reduced to a single root
  }

  /**
   *
   * @param s string to be processed
   * @param c character after which everything should  be removed
   * @return result of the processin
   */
  def removeAfterChar(s: String, c: Char): String = if (s.contains(c)) s.substring(0, s.indexOf(c)) else s

  private def truncateBefore(s: String, p: String) = {
    if (s.indexOf(p) == -1) s else s.substring(0, s.indexOf(p))
  }

  /** returns the name of the spatial variable, from the name of one of its bitplane component */
  def radicalOfVar(s: String): String = {
    truncateBefore(truncateBefore(s, "$"), "#")
  }

  /** returns the name of the spatial variable, from the name of one of its scalar component */
  def radicalOfVar2(s: String): String = {
    truncateBefore(s, "#")
  }

  /** returns the index of first non lowercase or string size if everything is uppercase. */
  def indexOfFirstUpperCase(v: String): Int = {
    var i = 0
    while (i < v.size && v(i).isLower) i = i + 1
    i
  }

  /** return the root defined as the longest prefix without upperCase */
  def rootOfVar(v: String) = {
    val i = indexOfFirstUpperCase(v)
    v.substring(0, i)
  }


  def indexOfLastUpperCase(v: String) = {
    val pat = Pattern.compile("[A-Z][^A-Z]*$")
    val `match` = pat.matcher(v)
    var lastCapitalIndex = -1
    if (`match`.find) lastCapitalIndex = `match`.start
    lastCapitalIndex
  }


  /** returns the name of the layers containing var, or empty string if there is none */
  def fatherOfVar(v: String): String = {
    if (Named.isLayer(v)) return v.substring(2)
    val i = indexOfLastUpperCase(v)
    if (i == -1) ""
    else v.substring(0, i)
  }

  def lastPathPart(v: String): String = {
    val i = indexOfLastUpperCase(v)
    if (i == -1) v
    else v.substring(i, v.size)
  }

  /** reconstruit les paramétres de type spatial */
  def shortenedSig(param: List[String]): List[String] = {
    val res: mutable.LinkedHashSet[String] = mutable.LinkedHashSet() //linked est la pour que l'ordre soit conservé
    for (p <- param) res += radicalOfVar(p)
    return res.toList;
  }

  // we now have method of generic use, which can  rotate sequences, or arrays.
  // or compose together arrays.
  def rotRn[T](seq: Seq[T], i: Int): Seq[T] = {
    val size = seq.size
    seq.drop(size - (i % size)) ++ seq.take(size - (i % size))
  }

  def rotL[T](a: Array[T])(implicit m: ClassTag[T]): Array[T] = a.drop(1) :+ a(0)

  def rotR[T](a: Array[T])(implicit m: ClassTag[T]): Array[T] = a(a.length - 1) +: a.take(a.length - 1)

  def rot[T](a: Array[T], dir: Boolean)(implicit m: ClassTag[T]): Array[T] = if (dir) Util.rotR(a) else Util.rotL(a)

  //dir=True correspond to trigonometric order
  def rotPerm(dec: Int): Array[Int] = {
    val r = new Array[Int](6);
    for (i <- 0 to 5) r(i) = (i + dec) % 6;
    r
  }

  def composeAll2(p: Array[Int], t: iTabSymb2[Array[Int]]): iTabSymb2[Array[Int]] = t.map { case (k, v) => k -> compose(p, v) }

  def composeAll(p: Array[Int], t: iTabSymb[Array[Int]]): Map[String, Array[Int]] = t.map { case (k, v) => k -> compose(p, v) }
}
