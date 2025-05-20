package simulator

import compiler.{Locus, copyEntireLine, getBitx, putBitx, rotateEntireLineLeft, rotateEntireLineRigt, rotateLeft, rotateRight}
import dataStruc.Util.{Rectangle, copyArray}
import simulator.UtilBitJava.{moveBitxtoy, propagateBitxand1}
import triangulation.Utility.{interleaveSpace, intsToLine, lineToInts, maskCompact, maskSparse, pop, push, unInterleaveSpace, writeInt32}

import scala.collection.immutable.HashMap
import scala.math.min


trait encodeByInt extends Rectangle {
  /** total  number of Int32 needed for one bit plane */
  def nbInt32total: Int

  /** Implements communication needed to propagete bits so that shifting can be implemented with just << or >>
   * and miroring line and columns, so that Gabriel centers will appear on border */
  def propagate4Shift: PrShift

  /**
   * encode from boolean to ints 32 bits
   *
   * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
   * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
   */
  def encode(memCAbool: Array[Array[Boolean]], memCAint32: Array[Int]): Unit

  /**
   * decodes, from Int 32 bits to booleans
   *
   * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
   * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
   * */
  def decode(memCAint32: Array[Int], memCAbool: Array[Array[Boolean]]): Unit

}

trait encodeGt extends encodeByInt {
  assert(nbCol % 30 == 0, "nbCol is a multiple of 30")
  /** number of ints needed storing the booleans of one bit plane of the CA memory */
  val nbInt32: Int = (nbLine * nbCol) / 30
  /** the number of "macro columns, two if nbColumn=60, a line is mapped to two columns, in a toroidal way." */
  val nbIntPerLine: Int = nbCol / 30
  val nbLineCAp1 = nbLine + 1 //number of int32 in a column
  /** we need to insert one integer as a buffer between each macro columns, plus two before and one after */
  val nbInt32total: Int = nbLineCAp1 * nbIntPerLine + 3
  val first = 2; //index of first integer of first line really used
  val last = nbLine + 1 //index of first integer of  last line really used

  override val propagate4Shift: PrShift = new PrShift() {
    def prepareBit(mem: Array[Int]): Unit = propage4Shift(mem)

    def prepareBit(mem: Array[Array[Int]]): Unit = mem.map(propage4Shift(_))

    def propage4Shift(mem: Array[Int]): Unit =
      for (i <- 0 until nbIntPerLine) //i index of a macro columns
        for (j <- i * nbLineCAp1 until (i + 1) * nbLineCAp1) //j traverse macro coloni
          UtilBitJava.propagateBit1and30(mem, 1 + j, 1 + (j + nbLineCAp1) % (nbIntPerLine * nbLineCAp1))

    override def mirror(mem: Array[Int], l: Locus): Unit = if (l.equals(Locus.locusV)) mirrorCopy(mem)
    override def mirror(mem: Array[Array[Int]], l: Locus): Unit = if (l.equals(Locus.locusV)) mem.map(mirrorCopy(_))

    /** do the copying part of mirroring */
    def mirrorCopy(mem: Array[Int]) = {
      def copyLine(src: Int, dest: Int) = copyEntireLine(mem, src + 1, dest + 1, nbIntPerLine, nbLineCAp1)
      def rotateLineRight(i: Int) = rotateEntireLineRigt(mem, i + 1, nbIntPerLine, nbLineCAp1)
      def rotateLineLeft(i: Int) = rotateEntireLineLeft(mem, i + 1, nbIntPerLine, nbLineCAp1)

      //process top line
      copyLine(2, 0)
      rotateLineRight(0) //a rotation of range 1, because the index diff is 2
      //process Bottom line
      copyLine(nbLine - 3, nbLine - 1)
      rotateLineLeft(nbLine - 1) //a rotation of range 1, because the index diff is 2

      //wenow process right and left column
      // we  precomputed  moves movesEven and movesOdd, which differ depending on the parity of the line index
      //we  have to move individual bits, because the moves are not uniform across considered integers
      val movesEven = HashMap[Int, Int](1 -> 0, (nbCol - 3) -> (nbCol - 1)) //here moves are between 0 and nbCOl-1
      val movesOdd = HashMap[Int, Int](2 -> 0, (nbCol - 2) -> (nbCol - 1))
      /** due to rotation, we must add a supplementary shift to even and odd,
       * shifted  moves are still  between 0 and nbCOl-1 */
      def shiftMv(h: Map[Int, Int], shiftRange: Int): Map[Int, Int] = {
        def shift(bitPos: Int, shiftRange: Int): Int = (bitPos + shiftRange + nbCol) % nbCol
        h.map({ case (k, v) => (shift(k, shiftRange), shift(v, shiftRange)) })
      }

      /**
       *
       * @param bitPos position of bit, between 0 and nbColCA
       * @param line   nummer of line within CA
       * @return index of int storing bitPos, and bit possition within this int, between 0 and 31
       */
      def intCoord(bitPos: Int, line: Int) = {
        val numBlock = nbIntPerLine - 1 - bitPos / 30
        val startCol = nbLineCAp1 * numBlock + 2 //first integer in target block
        //+2 because first two int not used
        (startCol + line, bitPos % 30 + 1) //, +1 because first bit is reserved for propagation from neighbor
      }

      /**
       *
       * @param mv   spefies src and target destination for a single bit, within a CA line of nbColCA cells
       * @param line index of line
       */
      def applyMove(mv: (Int, Int), line: Int, mem: Array[Int]) = {
        val (iIntSrc, ibitSrc) = intCoord(mv._1, line)
        val (iIntDest, ibitDest) = intCoord(mv._2, line)
        //for debug printMem(mem(iIntDest))
        val bitRead = getBitx(mem(iIntSrc), ibitSrc)
        mem(iIntDest) = putBitx(mem(iIntDest), ibitDest, bitRead)
        //for debug printMem(mem(iIntDest))
      }

      for (i <- first to last) {
        val moves = shiftMv(if (i % 2 == 0) movesEven else movesOdd, i / 2 - 1) //adds a shift i/2-1 to the move computed for the first line
        //the -1 comes for the fact that we start at 2
        for (mv <- moves) applyMove(mv, (i - 2), mem)
      }
    }

    /** does a torus on the border */
    override def torusify(h: Array[Array[Int]], l: Locus): Unit = ???

    override def torusify(h: Array[Int], l: Locus): Unit = ???
  }
  /**
   * encode from boolean to ints 32 bits
   * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
   * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
   */
  override def encode(memCAbool: Array[Array[Boolean]], memCAint32: Array[Int]): Unit = {
    //symetric case: we need several ints, in order to store one line of the CA
    for (i <- 0 until nbLine) { //we process line i whose length is nbColCA
      /** how much do we need to rotate right */
      val shift = (i / 2) % nbCol
      lineToInts(rotateLeft(memCAbool(i), shift), memCAint32, i * nbIntPerLine, min((i + 1) * nbIntPerLine, nbCol), nbIntPerLine, nbLine) //rotation is done on the whole CA lines.
    }
    interleaveSpace(memCAint32, nbIntPerLine, nbLine)
  }

  /**
   * decodes, from Int 32 bits to booleans
   *
   * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
   * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
   */
  override def decode(memCAint32: Array[Int], memCAbool: Array[Array[Boolean]]): Unit = {
    val tmp = copyArray(memCAint32)
    unInterleaveSpace(tmp, nbIntPerLine, nbLine)
    for (i <- 0 until nbLine) { //we iterate on the CA lines
      intsToLine(tmp, memCAbool(i), i * nbIntPerLine, min((i + 1) * nbIntPerLine, nbInt32), nbIntPerLine, nbLine)
      /** how much do we need to rotate right */
      val shift = (i / 2) % nbCol
      memCAbool(i) = rotateRight(memCAbool(i), shift).toArray //rotation is done on the whole CA lines.
    }
  }

}


trait encodeLt extends encodeByInt {
  val nbLignePerInt32 = 32 / (nbCol + 2)
  assert((nbCol == 6 || nbCol == 8 || nbCol == 14) && (nbLine % nbLignePerInt32) == 0, "nbCol must be  6, 8 or 14, all the int32 are used completely")
  /** number of ints needed storing the booleans of one bit plane of the CA memory */
  val nbInt32: Int = nbLine / nbLignePerInt32 //for each lines, we need two separating bits
  assert(nbInt32 % 2 == 0||nbInt32==1) //we need an even number of integers, so that each int will regroupe line with identical parity
  // which will result in a simpler scheme for implementing  the axial symmetry of vertical axis.
  /** number of Int32 needed for one bit plan of the CA memory * */
  def nbInt32total: Int = 4 + nbInt32 //we need two extra int32 before and two extra int32 after.

  override val propagate4Shift: PrShift = new PrShift() {
    def addMod(i: Int, j: Int) = (i + j + nbCol) % nbCol
    val first = 2;
    val last = 1 + nbInt32
    val maskS: Integer = maskSparse(nbCol)
    val bout = 32 % (nbCol + 2)
    /** we build the move computed for the first line* */
    val (movesEven, movesOdd) = {
      var even: Map[Int, Int] = HashMap.empty
      var odd: Map[Int, Int] = HashMap.empty
      var leftMost = 32 - bout - (nbCol + 2) + 1
      var destLeft = nbCol - 1 //index modulo nbCol of leftmost and right most value of line, place where we will copy
      while (leftMost > 0) //last considered value is 1
      {
        val destRight = addMod(destLeft, -nbCol + 1)
        even = even + (leftMost + addMod(destLeft, -2) -> (leftMost + destLeft))
        odd = odd + (leftMost + addMod(destLeft, -1) -> (leftMost + destLeft))
        even = even + (leftMost + addMod(destRight, +1) -> (leftMost + destRight))
        odd = odd + (leftMost + addMod(destRight, +2) -> (leftMost + destRight))
        leftMost -= nbCol + 2
        destLeft = addMod(destLeft, nbInt32 / 2) //le decalage augmente en rapport avec le nombre d'entier

        if (destLeft >= nbCol)
          throw new Exception("pb addmod")
      }
      (even, odd)
    }


    def prepareBit(mem: Array[Int]): Unit = propagate4Shift(mem)

    def prepareBit(mem: Array[Array[Int]]): Unit = mem.map(propagate4Shift(_))


    def propagate4Shift(mem: Array[Int]): Unit = {
      mem(first - 1) = mem(last) >>> (nbCol + 2) //we start by computing  the very first integer t[first-1]
      mem(last + 1) = mem(first) << (nbCol + 2) //and then the very last integer t[last+1]
      for (i <- 1 until last + 1)
        mem(i) = propagateBitxand1(mem(i), nbCol, maskS)
    }

    override def mirror(mem: Array[Int], l: Locus): Unit = if (l.equals(Locus.locusV)) mirrorCopy(mem)
    //else    throw new Exception("miror on non V")

    override def mirror(mem: Array[Array[Int]], l: Locus): Unit = if (l.equals(Locus.locusV)) mem.map(mirrorCopy(_))
    //else   throw new Exception("miror on non V")
    override def torusify(mem: Array[Int], l: Locus): Unit = if (l.equals(Locus.locusV)) torusifyCopy(mem)
    //else    throw new Exception("miror on non V")

    override def torusify(mem: Array[Array[Int]], l: Locus): Unit = if (l.equals(Locus.locusV)) mem.map(torusifyCopy(_))
    //else   throw new Exception("miror on non V")

    def torusifyCopy(mem: Array[Int]) = {

      def shift(h: Map[Int, Int], shiftRange: Int): Map[Int, Int] = {
        /** due to rotation, we must add a supplementary shift to the moves even and odd */
        def shift(i: Int, shiftRange: Int): Int = {
          val offset = i - i % (nbCol + 2)
          val iroot = i - offset - 1 //iroot is in the right interval 0..nbCol-1 so as to do a modulo addition
          val ishifted = addMod(iroot, shiftRange)
          val res = ishifted + offset + 1
          if (shiftRange == 0 && res != i) throw new Exception("shift Error")
          res
        }

        h.map({ case (k, v) => (shift(k, shiftRange), shift(v, shiftRange)) })
      }
      /** applies a precomputed list of move, (distinct for even or odd int32. */
      def applyMove(v: Int, moves: Map[Int, Int], mask: Int): Int = {
        var res = v
        for (move <- moves)
          res = moveBitxtoy(res, move._1, move._2, mask)
        res
      }
      //process top line
      val bout = 32 % (nbCol + 2)
      val maskFirst = maskCompact(nbCol) >> bout //cover the first line. we pass over the first two bits, for nbCol+2=10
      val line2 = if (nbInt32 > 2) mem(4) else mem(first) << nbCol + 2 //faut aussi rotationner les bits eux meme
      val line2Trunc = line2 & maskFirst
      val line2rotated = (line2Trunc >>> 1 | (line2Trunc << (nbCol - 1))) & maskFirst
      mem(first) = writeInt32(mem(first), line2rotated, maskFirst) //copy line 2, to line 0
      //process bottom line
      val maskOffset = (nbLignePerInt32 - 1) * (nbCol + 2)
      val maskLast = maskFirst >>> maskOffset
      val linem2 = if (nbInt32 > 2) mem(last - 2) else mem(last) >>> (nbCol + 2)
      val linem2Trunc = linem2 & maskLast //faut aussi rotationner les bits eux meme
      val linem2Rotated = (linem2Trunc << 1 | (linem2Trunc >>> (nbCol - 1))) & maskLast //& 0x00000002
      mem(last) = writeInt32(mem(last), linem2Rotated, maskLast) //copy line last-2, to last line
      //process right and left column using precomputed  moves in movesEven and movesOdd
      val maskSlim = 1 //we will now have to move bit by bit, because the moves are not uniform across a given integers
      for (i <- first - 1 until last + 1) {
        val mv = shift(if (i % 2 == 0) movesEven else movesOdd, i / 2 - 1) //adds a shift i/2-1 to the move computed for the first line
        mem(i) = applyMove(mem(i), mv, maskSlim)
      }
    }

    /** do the copying part of mirroring */
    def mirrorCopy(mem: Array[Int]) = {

      def shift(h: Map[Int, Int], shiftRange: Int): Map[Int, Int] = {
        /** due to rotation, we must add a supplementary shift to the moves even and odd */
        def shift(i: Int, shiftRange: Int): Int = {
          val offset = i - i % (nbCol + 2)
          val iroot = i - offset - 1 //iroot is in the right interval 0..nbCol-1 so as to do a modulo addition
          val ishifted = addMod(iroot, shiftRange)
          val res = ishifted + offset + 1
          if (shiftRange == 0 && res != i) throw new Exception("shift Error")
          res
        }

        h.map({ case (k, v) => (shift(k, shiftRange), shift(v, shiftRange)) })
      }

      /** applies a precomputed list of move, (distinct for even or odd int32. */
      def applyMove(v: Int, moves: Map[Int, Int], mask: Int): Int = {
        var res = v
        for (move <- moves)
          res = moveBitxtoy(res, move._1, move._2, mask)
        res
      }
      //process top line
      val bout = 32 % (nbCol + 2)
      val maskFirst = maskCompact(nbCol) >> bout //cover the first line. we pass over the first two bits, for nbCol+2=10
      val line2 = if (nbInt32 > 2) mem(4) else mem(first) << nbCol + 2 //faut aussi rotationner les bits eux meme
      val line2Trunc = line2 & maskFirst
      val line2rotated = (line2Trunc >>> 1 | (line2Trunc << (nbCol - 1))) & maskFirst
      mem(first) = writeInt32(mem(first), line2rotated, maskFirst) //copy line 2, to line 0
      //process bottom line
      val maskOffset = (nbLignePerInt32 - 1) * (nbCol + 2)
      val maskLast = maskFirst >>> maskOffset
      val linem2 = if (nbInt32 > 2) mem(last - 2) else mem(last) >>> (nbCol + 2)
      val linem2Trunc = linem2 & maskLast //faut aussi rotationner les bits eux meme
      val linem2Rotated = (linem2Trunc << 1 | (linem2Trunc >>> (nbCol - 1))) & maskLast //& 0x00000002
      mem(last) = writeInt32(mem(last), linem2Rotated, maskLast) //copy line last-2, to last line
      //process right and left column using precomputed  moves in movesEven and movesOdd
      val maskSlim = 1 //we will now have to move bit by bit, because the moves are not uniform across a given integers
      for (i <- first - 1 until last + 1) {
        val mv = shift(if (i % 2 == 0) movesEven else movesOdd, i / 2 - 1) //adds a shift i/2-1 to the move computed for the first line
        mem(i) = applyMove(mem(i), mv, maskSlim)
      }
    }
  }
  //PrepareShift.prepareShiftGte30

  /**
   * encode from boolean to ints 32 bits
   *
   * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
   * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
   *                   if nbColCA = 8 memCAint32(k) contains 4  block of 8 bits, the first one starting at position k, with a space of
   *                   nbLine/4 in between
   */
  override def encode(memCAbool: Array[Array[Boolean]], memCAint32: Array[Int]): Unit = {
    for (i <- 0 until nbLine) { //we iterate on the CA lines,
      /** how much do we need to rotate */
      val shift = (i / 2) % nbCol
      val rotated = rotateLeft(memCAbool(i), shift) // takes into account the fact that lines get shifted
      /** index of target Int32, which implements interleaving */
      val index = i % nbInt32
      memCAint32(index) = memCAint32(index) << 1 //separating bit
      memCAint32(index) = push(memCAint32(index), rotated)
      memCAint32(index) = memCAint32(index) << 1 //separating bit
    }
    interleaveSpace(memCAint32, 1, nbInt32) //insert the necessary spaces
  }

  /**
   * decodes, from Int 32 bits to booleans
   *
   * @param memCAbool  boolean bit plane isomorph to the Cellular AUtomaton structure
   * @param memCAint32 compressed form into a 1D array of 32 bits Integers, on which iteration will proceeds
   */
  override def decode(memCAint32: Array[Int], memCAbool: Array[Array[Boolean]]): Unit = {
    val tmp = copyArray(memCAint32)
    unInterleaveSpace(tmp, 1, nbInt32)
    for (i <- (0 until nbLine).reverse) {
      val index = i % nbInt32
      tmp(index) = tmp(index) >>> 1 //skipping separating bit
      tmp(index) = pop(tmp(index), memCAbool(i)) //lecture de la iéme ligne
      tmp(index) = tmp(index) >>> 1 //skipping separating bit
      /** how much do we need to rotate right */
      val shift = (i / 2) % nbCol
      memCAbool(i) = rotateRight(memCAbool(i), shift).toArray
    }
  }

}






