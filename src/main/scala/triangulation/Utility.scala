package triangulation

import dataStruc.Coord2D
import simulator.Controller

import java.awt.{Color, Polygon}
import java.lang.Integer.decode
import math.min
import scala.collection.immutable.HashMap
import scala.swing.Dimension

/** contains all the simple static functions needed for simulation plus some global variables*/
object Utility {

  /** max registered since last time */


  //color Utilities

  def halve(color: Color): Color = {
    val red = color.getRed
    val green = color.getGreen
    val blue = color.getBlue
    new Color(red / 2, green / 2, blue / 2)
  }

  def crop(c: Int) = {
   // maxRedGreenBlue(i)=Math.max(maxRedGreenBlue(i),c)
    Math.min(c, 255)
  }

  /**
   *
   * @param color
   * @param c added color, hence multiplied by coefficient
   *          @param darkness set by the simulator
   * @return
   */

  def addColor(color: Color, c: Color,darkness:Int): Color = {
    val red = crop(color.getRed + Math.ceil( (c.getRed*darkness)/100).toInt)
    val green = crop(color.getGreen +  Math.ceil( (c.getGreen*darkness)/100).toInt)
    val blue = crop(color.getBlue +  Math.ceil( (c.getBlue*darkness)/100).toInt)
    new Color(red, green, blue)
  }


  //compute an angle defined by three points, using the scalar product, and arcosinus, at the level of B
  def angle(A:Coord2D,B:Coord2D,C:Coord2D):Double={
    val BA=A.sub(B)
    val BC=C.sub(B)
    Math.acos(BA.prodScal(BC)/(BA.norme * BC.norme))
  }
  def addPoint(p: Polygon, a: Vector2D) =
    p.addPoint(a.x.toInt, a.y.toInt)

  def addPoints(p: Polygon, l: List[Vector2D]) =
    for (a <- l) addPoint(p, a)

  def toPolygon(l: List[Vector2D]) = {
    val p = new Polygon();
    addPoints(p, l);
    p
  }

  def fromPolygon(p: Polygon): List[Vector2D] = {
    val x = p.xpoints.toList
    val y = p.ypoints.toList
    (x zip y).map((p: (Int, Int)) => new Vector2D(p._1, p._2))
  }

  def toPolygon(t: Triangle2D): Polygon = toPolygon(List(t.a, t.b, t.c))

  private def vector2D(xy: (Int, Int)) = new Vector2D(xy._1, xy._2)

  def toPolygon(d: Dimension): Polygon = toPolygon(List((0, 0), (0, d.height), (d.width, d.height), (d.width, 0)).map(vector2D(_)))

  val epsilon = 1e-10

  def neglectable(d: Double) = Math.abs(d) < epsilon

  def time(operation: => Unit, operationName: String): Double = {
    val t0 = System.nanoTime()
    operation
    val time = (System.nanoTime() - t0) / 1e6
    println(operationName + "took ", time, "ms")
    return time
  }

  /** allume le nombre de bits correponsdants en début d'entier. faut faire +2 par exemple pour 8 ca allume 10 bits.
   * used to move entire lines */
  val maskCompact: Map[Int, Int] = HashMap(6 -> 0xFF000000, 8 -> 0xFFC00000, 14 -> 0xFFFF0000, 30 -> 0xFFFFFFFF)
  /** allume le nombre de bits correponsdants en début d'entier. faut faire +2 par exemple pour 8 ca allume 10 bits.
   * used to move entire lines */
  val maskCompactTighter: Map[Int, Int] = maskCompact.map{ case (k, v) => k -> (v & (v<<1)& (v>>>1)) }
  /** used to move bits within each line. */
  val maskSparse: Map[Int, Int] = HashMap(6 -> 0x01010101, 8 -> (1 | 1 << 10 | 1 << 20), 14 -> 0x00010001, 30 -> 0x00000001)

  def writeInt32(dest: Int, src: Int, mask: Int): Int =
    (dest & ~mask) | (src & mask)
  /**
   *
   * @param input Int storing a stack of bits
   * @param b     another bit, most significant bits pushed first, will be found to the left
   * @return stack updated by pushing b
   */
  def push(input: Int, b: Boolean): Int =
    (input << 1) | (if (b) 1 else 0) //<<1 multiple par 2

  /**
   *
   * @param input Int storing a stack of bits
   * @return new stack with one bit b popped, together with b*/
  def pop(input: Int): (Int, Boolean) = {
    val res: Boolean = (input & 1) == 1
    (input >>> 1, res)
  }

  /**
   *
   * @param input    integer storing a stack of bits
   * @param booleans input bits to stack, most significant bits first msb first
   * @return resulting stack
   */
  def push(input: Int, booleans: Seq[Boolean]): Int = {
    var res = input
    for (b: Boolean <- booleans)
      res = push(res, b)
    res
  }

  /**
   *
   * @param input    integer storing a stack of bits
   * @param booleans array to receive popped bit from this stack, msb first
   * @return pops the bits and return them in booleans,
   *         also returns the integer storing the resulting stack
   */
  def pop(input: Int, booleans: Array[Boolean]): Int = {
    var res = input
    for (v <- (0 until booleans.size).reverse) {
      val (newInput, b) = pop(res)
      booleans(v) = b
      res = newInput
    }
    res
  }

  /** THIS IS OBSOLETE
   *
   * @param l      input 2D array of boolean
   * @param iStart index at which we start to read boolean lines
   * @param iEnd   index at which we  finish to read boolean lines
   * @return Int32bits, storing the booleans as a stack
   */
  def linesTo1Int(l: Array[Array[Boolean]], iStart: Int, iEnd: Int): Int = {
    var res: Int = 0
    for (i <- iStart until iEnd)
      res = push(res, l(i))
    res
  }

  def interleaved(i: Int, nbBlock: Int, blockSize: Int) = (i % nbBlock) * blockSize + i / nbBlock

  /** unInterleave is like interleave, permuting block number and block size */
  def unInterleaved(i: Int, nbBlock: Int, blockSize: Int): Int = interleaved(i, blockSize, nbBlock)


  /**
   *
   * @param x          integer being shifted
   * @param firstshift number of bits to shift (like x<<firstshift or x>>firstshift in C++)
   * @param bits       the number of bits you want to have/emulate, ...
   * @return
   */
  def rol(x: Int, firstshift: Int, bits: Int = 32): Int = {
    if (firstshift < 0) return ror(x, -firstshift, bits)
    val shift = firstshift % bits
    // masks                           |       bits        |
    val m0 = (1 << (bits - shift)) - 1 // |0000000|11111111111|
    // | shift |           |
    val m1 = (1 << shift) - 1 // |00000000000|1111111|
    // |           | shift |
    ((x & m0) << shift) | ((x >>> (bits - shift)) & m1)
  }

  //---------------------------------------------------------------------------
  def ror(x: Int, firstshift: Int, bits: Int = 32): Int = {
    if (firstshift < 0) return rol(x, -firstshift, bits)
    val shift = firstshift % bits
    val m0 = (1 << (bits - shift)) - 1
    val m1 = (1 << shift) - 1
    ((x >>> shift) & m0) | ((x & m1) << (bits - shift))
  }

  import compiler.rotateRight
  import compiler.rotateLeft

  /**
   *
   * @param lCA    input 1D array of boolean of size>=30
   * @param lCAmem array of 32bits int, where to pack those booleans as integer
   * @param iStart starting index in lCAmem where to start packing
   * @param iEnd   lastIndex in lCAmem where to finish packing
   * @return LCS has one more int containing 30 bits (or less) of a line of LCA
   */
  def lineToInts(lCA: Seq[Boolean], lCAmem: Array[Int], iStart: Int, iEnd: Int, nbBlock: Int, blockSize: Int) = {
    for (i <- iStart until iEnd) { // indexes of  target Int32 of LCAmem, if we were not interleaving
      assert(iStart<iEnd)
      var int32: Int = 0
      //for(j<-0 until lCA.size)
      for (j <- (i - iStart) * 30 until min((i + 1 - iStart) * 30, lCA.size)) // j visits the indexes of the portion in the considered LCA lines
        int32 = push(int32, lCA(j))
      //lCAmem(i) = int32 << 1 //<<1 leave the place  for the communication bit
      val i2 = interleaved(i, nbBlock, blockSize)
      lCAmem(i2) = int32 << 1 //<<1 leave the place  for the communication bit
    }
  }


  def move(t: Array[Int], i: Int, i1: Int, blockSize: Int) =
    for (j <- (0 until blockSize).reverse)
      t(i1 + j) = t(i + j)

  def moveBack(t: Array[Int], i: Int, i1: Int, blockSize: Int) =
    for (j <- (0 until blockSize))
      t(i + j) = t(i1 + j)

  /** in a second step, we create  space between block so has to be able to shift only with << or >> */
  def interleaveSpace(memCAint32: Array[Int], nbBlock: Int, blockSize: Int) = {
    for (i <- (0 until nbBlock).reverse)
      move(memCAint32, i * blockSize, 2 + i * (blockSize + 1), blockSize)
    for (i <- (0 until nbBlock).reverse) //we explicitely enter zero in the spaces, otherwise it would trigger bug
      memCAint32(2 + i * (blockSize + 1) -1)=0
  }

  def unInterleaveSpace(memCAint32: Array[Int], nbBlock: Int, blockSize: Int) =
    for (i <- (0 until nbBlock))
      moveBack(memCAint32, i * blockSize, 2 + i * (blockSize + 1), blockSize)


  /**
   * @param nbColCA    the number of columns in the CA
   * @param nbLineCA   the number of lines in the CA
   * @param memCAbool  a list of booleans processed by the CA, supplied as data
   * @param memCAint32 a list of 32bits integer packing the booleans
   * @return lCAmem is computed from lCA
   *         we add interleaving and rotation
   *         when we  rotate to the right , the LSB is moved and this amounts to dividing by 2.
   */
  def encodeInterleavRot(nbLineCA: Int, nbColCA: Int, memCAbool: Array[Array[Boolean]], memCAint32: Array[Int]) = {
    assert(nbLineCA == memCAbool.size)
    assert(nbColCA == memCAbool(0).size)
    val nbInt32used = (nbLineCA * nbColCA) / 30 //carefull:that is distinct from memCAbool.size
    if (nbColCA <= 30) { //one int32 stores  several CA lines.we need to spare 2 bits for communication.
      assert(30 % nbColCA == 0, "each int32 must be responsible for the same number of small CA lines")
      for (i <- 0 until nbLineCA) { //we iterate on the CA lines,
        /** index of target Int32, which implements interleaving */
        val index = i % nbInt32used
        memCAint32(index) = push(memCAint32(index), memCAbool(i))
      }
      for (i <- 0 until nbInt32used) { // each int32  needs to be rotated right
        /** how much do we need to rotate right */
        val shift = (i / 2) % nbColCA
        memCAint32(i) = rol(memCAint32(i), shift, 30) << 1
      }
      interleaveSpace(memCAint32, 1, nbInt32used)
    }
    else { //symetric case: we need several ints, in order to store one line of the CA
      /** number of int32 needed to represent one CA line */
      val nbIntColCA = nbColCA / 30 //this is gonna be >=2, two bits are devoted to communication
      for (i <- 0 until nbLineCA) { //we process line i whose length is nbColCA
        /** how much do we need to rotate right */
        val shift = (i / 2) % nbColCA
        lineToInts(rotateLeft(memCAbool(i), shift), memCAint32, i * nbIntColCA, min((i + 1) * nbIntColCA, nbColCA), nbIntColCA, nbLineCA) //rotation is done on the whole CA lines.
      }
      interleaveSpace(memCAint32, nbIntColCA, nbLineCA)
    }

  }

  def encodeInterleavRotOld(nbLineCA: Int, nbColCA: Int, memCAbool: Array[Array[Boolean]], memCAint32: Array[Int]) = {
    assert(nbLineCA == memCAbool.size)
    assert(nbColCA == memCAbool(0).size)

    if (nbColCA <= 30) { //one int32 stores  several CA lines.we need to spare 2 bits for communication.
      val nbInt32used = (nbLineCA * (nbColCA + 2)) / 32 //carefull:that is distinct from memCAbool.size
      assert(32 % (nbColCA + 2) == 0, "nbColCA =6 or 8")
      for (i <- 0 until nbLineCA) { //we iterate on the CA lines,
        /** how much do we need to rotate right */
        val shift = (i / 2) % nbColCA
        val rotated = rotateLeft(memCAbool(i), shift)
        /** index of target Int32, which implements interleaving */
        val index = i % nbInt32used
        memCAint32(index) = memCAint32(index) << 1 //separating bit
        memCAint32(index) = push(memCAint32(index), rotated)
        memCAint32(index) = memCAint32(index) << 1 //separating bit
      }
      //insert the necessary spaces
      interleaveSpace(memCAint32, 1, nbInt32used)
    }
    else { //symetric case: we need several ints, in order to store one line of the CA
      /** number of int32 needed to represent one CA line */
      val nbIntColCA = nbColCA / 30 //this is gonna be >=2, two bits are devoted to communication
      for (i <- 0 until nbLineCA) { //we process line i whose length is nbColCA
        /** how much do we need to rotate right */
        val shift = (i / 2) % nbColCA
        lineToInts(rotateLeft(memCAbool(i), shift), memCAint32, i * nbIntColCA, min((i + 1) * nbIntColCA, nbColCA), nbIntColCA, nbLineCA) //rotation is done on the whole CA lines.
      }
      interleaveSpace(memCAint32, nbIntColCA, nbLineCA)
    }

  }


  /**
   *
   *
   * @param lCAmem input array of 32bits int, where booleans are packed as integer
   * @param lCA    output  1D array of boolean of size>30
   * @param iStart starting index in lCAmem where to start unpacking
   * @param iEnd   lastIndex where to finish unpacking
   * @return
   */
  def intsToLine(lCAmem: Array[Int], lCA: Array[Boolean], iStart: Int, iEnd: Int, nbBlock: Int, blockSize: Int) = {

    for (i <- iStart until iEnd) {
      // var res: Int = lCAmem(i) >>> 1 //>>> ignore the communication bit
      val i2 = interleaved(i, nbBlock, blockSize)
      var res: Int = lCAmem(i2) >>> 1 //>>> ignore the communication bit
      for (j <- ((i - iStart) * 30 until min((i + 1 - iStart) * 30, lCA.size)).reverse) { //unpacking the 30 bits in LCA(i) in reverse order because of the stack
        val (newRes, b) = pop(res)
        res = newRes
        lCA(j) = b
      }
    }
  }

  /**
   * @param nbColCA    the number of columns in the CA
   * @param nbLineCA   the number of lines in the CA
   * @param memCAbool  a list of booleans processed by the CA, supplied as data
   * @param memCAint32 a list of 32bits integer packing the booleans
   * @return lCA is compurotateLeftted from lCAmem
   *         we rotate to the Left when decoding, the MSB is moved and this amounts to  multiplying by 2.
   */
  def decodeInterleavRot(nbLineCA: Int, nbColCA: Int, memCAint32: Array[Int], memCAbool: Array[Array[Boolean]]) = {
    assert(nbLineCA == memCAbool.size)
    assert(nbColCA == memCAbool(0).size)

    val tmp = Array.ofDim[Int](memCAint32.size) //we use tmp in order to not modify the CA memory
    for (i <- 0 until memCAint32.size)
      tmp(i) = memCAint32(i)
    if (nbColCA < 30) { //one int32 stores one or several sub= lines.
      /*      val nbInt32used = (nbLineCA*(nbColCA+2))/32
            assert(32 % (nbColCA+2) == 0, "each int32 must be responsible for the same number of small CA lines")
            /** each int32  needs to be rotated left */
            unInterleaveSpace(tmp,1,nbInt32used)
            for (i <- (0 until nbLineCA).reverse) {
              val index = i % nbInt32used
              tmp(index)=tmp(index) >>>1 //separating bit
              tmp(index) = pop(tmp(index), memCAbool(i)) //lecture de la iéme ligne
              tmp(index)=tmp(index) >>>1 //separating bit
              /** how much do we need to rotate right */
              val shift = (i / 2) % nbColCA
              memCAbool(i)=rotateRight(memCAbool(i), shift).toArray
            }*/

      val nbInt32used = (nbLineCA * (nbColCA)) / 30
      unInterleaveSpace(tmp, 1, nbInt32used)
      for (i <- 0 until nbInt32used)
        tmp(i) = tmp(i) >>> 1
      for (i <- 0 until nbInt32used) { //we start by applying left rotation
        /** how much do we need to rotate left */
        val shift = (i / 2) % nbColCA
        tmp(i) = ror(tmp(i), shift, 30)
      }
      for (i <- (0 until nbLineCA).reverse) { //we iterate downward, because integer are used as stacks,
        /** index of target Int32 */
        val index = i % nbInt32used //result from interleaving
        tmp(index) = pop(tmp(index), memCAbool(i))
      }
    }
    else { //symetric case: we need several ints, in order to store one line of the CA
      /** number of int32 needed to represent one CA line */
      val nbInt32used = (nbLineCA * nbColCA) / 30
      val nbIntColCA = nbColCA / 30 //this is gonna be >=2, two bits are devoted to communication
      unInterleaveSpace(tmp, nbIntColCA, nbLineCA)
      for (i <- (0 until nbLineCA)) { //we iterate on the CA lines
        intsToLine(tmp, memCAbool(i), i * nbIntColCA, min((i + 1) * nbIntColCA, nbInt32used), nbIntColCA, nbLineCA)
        /** how much do we need to rotate right */
        val shift = (i / 2) % nbColCA
        memCAbool(i) = rotateRight(memCAbool(i), shift).toArray //rotation is done on the whole CA lines.
      }
    }
  }


}
