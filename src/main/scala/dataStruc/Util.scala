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
import compiler.Locus.allLocus
import compiler.{T, _}
import dataStruc.Util.{CustomClassLoader, customClassLoader, loadClassAndInstantiate, sameElements}
import simulator.CAloops2
import triangulation.{DelaunayTriangulator, NotEnoughPointsException, Triangle2D, Vector2D, Voroonoi}

import java.util
import javax.tools.{JavaCompiler, StandardJavaFileManager, ToolProvider}
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


import java.io.{File, FileInputStream, IOException}
import java.net.URLClassLoader


object Util {

   //def orderDisplayed(displayed:List[String])



  /** returns name of already defined macro of type macrosType.
   *  for example, methods of rand, if macroTypeFile=compiledMacro/rand*/
  def myGetDeclaredMethod(macrosTypeFile: String): Array[String] = {
    try {
      val c: Class[_] = Class.forName(macrosTypeFile)
      c.getDeclaredMethods.map(_.getName())
    }
    catch{
      case e: ClassNotFoundException =>  Array() //on trouve pas grad, y a rien dedans
      case e: NoSuchMethodException =>
        println("Méthode introuvable: " + e.getMessage);Array()
      case e: SecurityException =>
        println("Problème de sécurité: " + e.getMessage);Array()
      case e:   NoSuchMethodException =>
        println("nosuchmethod"+ e.getMessage);Array()
      case e: Exception =>
        println("Exception inattendue: " + e.getMessage);Array()


    }
  }

  import java.net.URLClassLoader
  import java.io.File

  /**
   *
   * @param path where to find a compiledCA */  //todo enlever CAloops2
  def loadClass(path: String): Class[CAloops2] = {
    var res: Class[CAloops2] = null;
    try {
      res = Class.forName(path).asInstanceOf[Class[CAloops2]];
    }
    catch {
      case e: ClassNotFoundException =>
        System.out.println("la classe " + path + " n'existe  pas");
    }
    return res;
  }

  def getProg(progClass: Class[CAloops2]): CAloops2 = {
    var res: CAloops2 = null
    try res = progClass.getDeclaredConstructor().newInstance()
    catch {
      case e: InstantiationException =>
        e.printStackTrace()
      case e: IllegalAccessException =>
        e.printStackTrace()
    }
    res
  }
  // Custom ClassLoader that loads classes from a specified directory
  class CustomClassLoader(directory: String) extends URLClassLoader(Array(new File(directory).toURI.toURL), getClass.getClassLoader) {
    override def findClass(name: String): Class[_] = {
      try {
        super.findClass(name)
      } catch {
        case e: ClassNotFoundException =>
          throw new ClassNotFoundException(s"Could not load class $name from $directory", e)
      }
    }
  }

  // Function to load and instantiate a class using the custom class loader
  def loadClassAndInstantiate(className: String, classLoader: CustomClassLoader): Any = {
    val clazz = classLoader.loadClass(className)
    clazz.getDeclaredConstructor().newInstance() // Instantiate the class
  }

  // Directory where compiled classes are stored
  val classOutputDirectory = "target/scala-2.13/classes"

  // Create a custom class loader pointing to the directory with the newly compiled bytecode
  val customClassLoader = new CustomClassLoader(classOutputDirectory)

  /**
   *
   * @param fileCompiledName
   * @return true if the file exists
   */
  def existInJava( fileCompiledName :String):Boolean={
    val fileCompiled=new File (fileCompiledName)
    val res=fileCompiled.exists()
    res
  }

  /**
   *
   * @param fileprogName source scala
   * @param fileCompiledName compiled java
   * @return true if source scala has changed, since last compilation into java   */
  def hasBeenReprogrammed(fileprogName: String, fileCompiledName :String):Boolean={
    val fileProg=new File (fileprogName)
    val fileCompiled=new File (fileCompiledName)
    val e=fileProg.exists()
    val dp=fileProg.lastModified()
    val dc=fileCompiled.lastModified()
    val res= fileCompiled.exists() && fileProg.lastModified()>fileCompiled.lastModified()
    res
  }
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
        //println(s"Value of static field $fieldName: $fieldValue");
        fieldValue.asInstanceOf[Int]
      } else {
       // println(s"Field $fieldName is not static.");
        -1
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

  def prefixDot(s:String)={
    assert(s.contains("."),"string "+s+"shoud contain a point .")
    s.substring(0, s.indexOf("."))
  }
  def suffixDot(s: String)={
    assert(s.contains("."),"string "+s+"shoud contain a point .")
    s.drop(s.indexOf(".") + 1)
  }
  def prefixDash(s:String)= {
    assert(s.contains("_"),"string "+s+"shoud contain a dash")
    s.substring(0, s.indexOf("_"))
  }

  //def javaFileUrl(s:String)=radical(s)+"."+radicalRad(methodName(s))
  def suffixDash(s:String)=s.drop( s.indexOf("_"))
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
    bw.flush()
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
    val sons: List[String] = father2son(root).toList.sorted.reverse
    val (fieldDir,fields)=sons.partition(father2son.contains(_))
    val (hashmapField,fifields)=fields.partition(_.contains("yyy"))
    val orderedSons: List[String] =fieldDir:::hashmapField:::fifields
    root + "(" + orderedSons.map(parenthesizedExp(_, father2son)).mkString(")(") + ")" // + "." //the point is necessaru when the tree is reduced to a single root
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

  def componentNumber(chaine:String)= chaine.substring(chaine.indexOf("#") + 1)

  /** checks that the params correspond to select a given component */
  def checkSingleComponentNumber(params:List[String])={
    val components:Set[Int]=params.map(componentNumber(_).toInt).toSet
    if(components.size!=1)
      throw new Exception("ben non y en a plus que une composante")
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

  def dupliqueOrTriplique(a:Array[Int]): Array[Int]={
    assert(a.size<6) //sinon y a rien a faire!
    val result: Array[Int]=new Array(6)
    val fanout=6/a.length
    for(i<-0 until a.length)
      for(j<-0 until fanout)
        result(i*fanout+j)=a(i)
    result
  }

  def composeAll2(p: Array[Int], t: iTabSymb2[Array[Int]]): iTabSymb2[Array[Int]] = t.map { case (k, v) => k -> compose(p, v) }

  def composeAll(p: Array[Int], t: iTabSymb[Array[Int]]): Map[String, Array[Int]] = t.map { case (k, v) => k -> compose(p, v) }


  def compileJavaFiles(javaFiles: List[String]): Boolean = {
    // Obtain the Java compiler from the ToolProvider
    val compiler: JavaCompiler = ToolProvider.getSystemJavaCompiler

    // Get the standard file manager
    val fileManager: StandardJavaFileManager = compiler.getStandardFileManager(null, null, null)

    // Set the output directory for compiled classes
    val classOutputDirectory = new File("target/scala-2.13/classes")
    classOutputDirectory.mkdirs() // Ensure the target directory exists

    // Specify the output location for the file manager
    fileManager.setLocation(javax.tools.StandardLocation.CLASS_OUTPUT, List(classOutputDirectory).asJava)

    // Convert file paths to File objects
    val fileObjects = fileManager.getJavaFileObjectsFromStrings(javaFiles.asJava)

    // Compile the files
    val task = compiler.getTask(null, fileManager, null, null, null, fileObjects)

    val success = task.call() // true if compilation succeeds
    fileManager.close() // Close the file manager
    success
  }
}
