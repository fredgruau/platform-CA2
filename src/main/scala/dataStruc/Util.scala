package dataStruc

import compiler.Circuit.{iTabSymb, iTabSymb2}
import dataStruc.Align2.compose
import simulator.CAtype.pointLines
import triangulation.Vector2D
import triangulation.Vector2D.almostEqualS

import java.io.{BufferedWriter, File, FileWriter}
import java.lang.reflect.Field
import java.util.regex.Pattern
import scala.collection.immutable.HashMap
import scala.collection.{Map, Seq, mutable}
import scala.reflect.ClassTag


object Util {


  import compiler.Locus.allLocus
  import compiler.{T, _}
  import dataStruc.Util.sameElements
  import triangulation.{DelaunayTriangulator, NotEnoughPointsException, Triangle2D, Vector2D, Voroonoi}

  import java.util
  import scala.::
  import scala.math.cos
  //import de.alsclo.voronoi.graph.Voronoi
  import simulator.CAtype.pointLines
  import simulator.UtilBitJava.{moveBitxtoy, propagateBit14and1, propagateBit6and1, propagateBitxand1}
  import simulator.{Controller, Env, PrShift, UtilBitJava}
  import triangulation.Utility._

  import java.awt.Color
  import scala.collection.IterableOnce.iterableOnceExtensionMethods
  import scala.collection.JavaConverters._
  import scala.collection.immutable.{HashMap, HashSet}
  import scala.math.{min, random, round}
  import scala.swing.Dimension
  import scala.swing.Swing.pair2Dimension


  def readStaticField(className: String, fieldName: String): Int = {
    try {
      // Load the class by name
      val clazz: Class[_] = Class.forName(className)

      // Get the field by name
      val field: Field = clazz.getField(fieldName)

      // Ensure the field is static and public
      if (java.lang.reflect.Modifier.isStatic(field.getModifiers)) {
        // Get the value of the static field and print it
        val fieldValue: Any = field.get(null)  // `null` because it's a static field
        println(s"Value of static field $fieldName: $fieldValue"); fieldValue.asInstanceOf[Int]
      } else {
        println(s"Field $fieldName is not static.");-1
      }

    } catch {
      case e: ClassNotFoundException =>
        println(s"Class $className not found.");-1
      case e: NoSuchFieldException =>
        println(s"Field $fieldName not found in class $className.");-1
      case e: IllegalAccessException =>
        println(s"Cannot access field $fieldName in class $className.");-1
      case e: Exception =>
        e.printStackTrace();-1
    }

  }

  trait border{
    def boundingBox: Dimension
    def right(v:Vector2D):Boolean=almostEqualS(v.x,boundingBox.width);
    def left(v:Vector2D):Boolean=almostEqualS(v.x,0);
    def up(v:Vector2D):Boolean=almostEqualS(v.y,boundingBox.height);
    def down(v:Vector2D):Boolean=almostEqualS(v.y,0)
    def onBorder(v:Vector2D):Boolean={up(v)||down(v)||left(v)||right(v)}
    def onBorder(v:Vertex2):Boolean=onBorder(new Vector2D(v.coord.x,v.coord.y ))
    def onBorder(v:Coord2D):Boolean=onBorder(new Vector2D(v.x,v.y ))
    def onSameBorder(v1:Vector2D, v2:Vector2D)= {
      up(v1)&&up(v2)||
        down(v1)&&down(v2)||
        left(v1)&&left(v2)||
        right(v1)&&right(v2)
    }
  }

  def radical(s:String)={
    assert(s.contains("."),"string "+s+"shoud contain a point .")
    s.substring(0, s.indexOf("."))
  }
  def methodName(s: String)={
    assert(s.contains("."),"string "+s+"shoud contain a point .")
    s.drop(s.indexOf(".") + 1)
  }
  def radicalRad(s:String)= {
    assert(s.contains("_"),"string "+s+"shoud contain a dash")
    s.substring(0, s.indexOf("_"))
  }

  //def javaFileUrl(s:String)=radical(s)+"."+radicalRad(methodName(s))
  def dashPart(s:String)=s.drop( s.indexOf("_"))
  def intBetweenDash(s: String):List[Int]={
    if (s.length==0)List()
    else
    s(0) match{
      case '_'=> intBetweenDash(s.drop(1))
      case _ =>
        assert(s(0).isDigit,"sting "+s+ " should containts only dashes and digits")
        val res=s(0).toString.toInt
        res::intBetweenDash(s.drop(1))
    }

  }

  trait Rectangle{
    def nbLine: Int
    def nbCol: Int
    /**
     *
     * @param ni input to test
     * @param n  maximum allowed
     * @return true if 0<=ni<=n
     */
    private def insideInterval(ni: Int, n: Int) = 0 <= ni && ni < n
    /**
     *
     * @param ni input x coordinate
     * @param nj input y coordinate
     * @return true if the coordinates indicate a point within the cellular automaton
     */
    def inside(ni: Int, nj: Int) = insideInterval(ni, nbLine) && insideInterval(nj, nbCol)
  }

  def copyArray(t: Array[Int]): Array[Int] = {
    val tmp = Array.ofDim[Int](t.length) //we use tmp when decoding in order to to avoid modify the CA memory
    t.copyToArray(tmp)
    tmp
  }
  /** Removes an elements for a set and returns it
   * @return element removed */
  def pop[A] (s:mutable.HashSet[A]):A={
    val elem=s.head
    s.remove(elem)
    elem
  }


  def sameElements[T](t1:Array[pointLines],t2:Array[pointLines]): Boolean = {
    for (i <- 0 until t1.length)
      for (j <- 0 until t1(0).length)
        for (k <- 0 until t1(0)(0).length)
        { val tt1=t1(i)(j)
          val tt2=t2(i)(j)
          if (tt1(k).isDefined && (!tt1(k).get.almostEqual(tt2(k).get)))
            return false
        }
    return true
  }

  def writeFile(filename: String, s: String): Unit = {
    val file = new File(filename)
    println("Writing to file: " + file.getAbsolutePath) // Print file path for debugging

    val bw = new BufferedWriter(new FileWriter(file))
    try {
      bw.write(s)
      bw.flush()  // Ensure that the data is flushed to the file
    } finally {
      bw.close()  // Close the writer to release system resources
    }
  }

  def writeFileOld(filename: String, s: String): Unit = {
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

  /** If we directly set the name of a variable, the danger is that its name will not encode a path in layer, and therefore, will not be displayed */
  def sameRoot(displayed: Set[String]): Boolean =
    displayed.map(rootOfVar(_)).size == 1
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

  /** is s==# , turns toto#2 into [2] */
  def truncateAfterAndCrochetize(s: String, p: String) = {
    if (s.indexOf(p) == -1) "" else "[" + s.substring(s.indexOf(p) + 1, s.length) + "]"
  }

  /** returns toto from toto#2 */
  def radicalOfVar(s: String): String = {
    truncateBefore(truncateBefore(s, "$"), "#")
  }

  /** turns toto#2 into toto[2] */
  def radicalOfVarIntComp(s: String): String = {
    radicalOfVar(s) + truncateAfterAndCrochetize(s, "#")
  }

  /** replace toto#2  by toto[2] is all members contains either a diese or a dollar */
  def radicalOfVarRefined(params: List[String]) = {
    val allParamDieseorDollar = params.map(s => s.contains('#') || s.contains('$')).reduce(_ && _)
    if (allParamDieseorDollar)
      params.map(radicalOfVar(_))
    else
      params.map(radicalOfVarIntComp(_))
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
    for (p <- param) res += radicalOfVar(p) //comme on a un ensemble les doublons seront fusionné.
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
