package simulator

import compiler.{Locus, copyEntireLine, getBitx, putBitx, rotateEntireLineLeft, rotateEntireLineRigt, rotateLeft, rotateRight}
import dataStruc.Util.{Rectangle, copyArray, isMiror, miror}
import simulator.UtilBitJava.{moveBitxtoy, propagateBitxand1}
import triangulation.Utility.{interleaveSpace, intsToLine, lineToInts, maskCompact, maskCompactTighter, maskSparse, pop, push, unInterleaveSpace, writeInt32}

import scala.collection.immutable.HashMap
import scala.math.min


trait encodeByInt extends Rectangle {
  /** total  number of Int32 needed for one bit plane */
  def nbInt32total: Int

  /** Implements communication needed to propagete bits so that shifting can be implemented with just << or >>
   * and miroring line and columns, so that Gabriel centers will appear on border
   * and also torusifying for random numbers. */
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

  /** return true if it is in mirrored form. It is a slow but easy and safe implementation, used for debug*/
  def isMirorSafe(memCAint32: Array[Int]):Boolean={
    val lCAoutput = Array.ofDim[Boolean](nbLine, nbCol)
    decode(memCAint32, lCAoutput)
    isMiror(lCAoutput)
  }
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


  /** instancie une classe abstraite java. */
  override val propagate4Shift: PrShift = new PrShift() {
    /** is miror is defined in Prshift, so that it can be called back  during the execution of  the CA loops */
    override def isMirrorSafe(h: Array[Int]): Boolean = encodeGt.super.isMirorSafe(h)
    def prepareBit(mem: Array[Int]): Unit =  {
      if(nbIntPerLine>=1) //rajoue pour faire le propagate si vraiment c'est necessaire
        for (i <- 0 until nbIntPerLine) //i index of a macro columns faut probablement faire une iération de moins
          for (j <- i * nbLineCAp1 until (i + 1) * nbLineCAp1) //j traverse macro coloni
            UtilBitJava.propagateBit1and30(mem, 1 + j, 1 + (j + nbLineCAp1) % (nbIntPerLine * nbLineCAp1))
    }

    def mirror(mem: Array[Int]): Unit =
      {
        mirrorCopyFast(mem)
       // assert(isMirrorSafe(mem)) //la verif coute cher en temps, on la remet en cas de pb
      }

    /** do the copying part of mirroring in a safe but time expensive way. Used for punctual testing in case of problem */
    def mirrorCopySafe(mem: Array[Int]) = {
      val matBool=Array.ofDim[Boolean](nbLine,nbCol)
      decode(mem,matBool)
      miror(matBool)
      encode(matBool,mem)
    }

    /** does a torus on the border */

    override def torusify(h: Array[Int]): Unit = torusifyFast(h)

    def copyLine(mem: Array[Int],src: Int, dest: Int) = copyEntireLine(mem, src + 1, dest + 1, nbIntPerLine, nbLineCAp1)
    def rotateLineRight(mem: Array[Int],i: Int) = rotateEntireLineRigt(mem, i + 1, nbIntPerLine, nbLineCAp1)
    def rotateLineLeft(mem: Array[Int],i: Int) = rotateEntireLineLeft(mem, i + 1, nbIntPerLine, nbLineCAp1)

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

    /**  mirroring in complex effficient form */
    def mirrorCopyFast(mem: Array[Int]) = {
      //process top line
      copyLine(mem,2, 0);  rotateLineRight(mem,0) //a rotation of range 1, because the index diff is 2
      //process Bottom line
       copyLine(mem,nbLine - 3, nbLine - 1);  rotateLineLeft(mem,nbLine - 1) //a rotation of range 1, because the index diff is 2

      //wenow process right and left column
      // we  precomputed  moves movesEven and movesOdd, which differ depending on the parity of the line index
      //we  have to move individual bits, because the moves are not uniform across considered integers
      val movesEven = HashMap[Int, Int](1 -> 0, (nbCol - 3) -> (nbCol - 1)) //here moves are between 0 and nbCOl-1
      val movesOdd = HashMap[Int, Int](2 -> 0, (nbCol - 2) -> (nbCol - 1))
      for (i <- first to last) {
        val moves = shiftMv(if (i % 2 == 0) movesEven else movesOdd, i / 2 - 1) //adds a shift i/2-1 to the move computed for the first line
        //the -1 comes for the fact that we start at 2
        for (mv <- moves) applyMove(mv, (i - 2), mem)
      }
    }
    def torusifyFast(mem: Array[Int])={
      //vertical torify
      // process top line
      copyLine(mem,nbLine - 2, 0)
      val nbRot=((nbLine-2)/2)%30
      for(i<- 0 until nbRot ) rotateLineRight(mem,0)
      //process Bottom line
      copyLine(mem,1, nbLine - 1)
      for(i<- 0 until nbRot ) rotateLineLeft(mem,nbLine - 1)
      //horizontal torrify
      val movesTorify=HashMap[Int, Int]((nbCol - 2) -> 0, 1-> (nbCol - 1))
      for (i <- first to last) {
        val moves: Map[Int, Int] = shiftMv(movesTorify, i / 2 - 1) //adds a shift i/2-1 to the move computed for the first line
        //the -1 comes for the fact that we start at 2
       for (mv <- moves)    applyMove(mv, (i - 2), mem)
      }
      val z=0
    }

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

    val (movesEven, movesOdd,moveTorify) = {
      var even: Map[Int, Int] = HashMap.empty
      var odd: Map[Int, Int] = HashMap.empty
      var moveTorify: Map[Int, Int] = HashMap.empty
      var leftMost = 32 - bout - (nbCol + 2) + 1
      var destLeft = nbCol - 1 //index modulo nbCol of leftmost and rightmost value of line, place where we will copy
      while (leftMost > 0) //last considered value is 1
      {
        val destRight = addMod(destLeft, -nbCol + 1)
        even = even + (leftMost + addMod(destLeft, -2) -> (leftMost + destLeft))
        odd = odd + (leftMost + addMod(destLeft, -1) -> (leftMost + destLeft))
        even = even + (leftMost + addMod(destRight, +1) -> (leftMost + destRight))
        odd = odd + (leftMost + addMod(destRight, +2) -> (leftMost + destRight))
        //on arrive a construire les moveTorify, en observant les odd et even
        moveTorify = moveTorify + (  (leftMost + addMod(destRight, +1) )->  (leftMost + destLeft))
        moveTorify = moveTorify+  ( (leftMost + addMod(destLeft, -1)) -> (leftMost + destRight) )
        leftMost -= nbCol + 2
        destLeft = addMod(destLeft, nbInt32 / 2) //le decalage augmente en rapport avec le nombre d'entier

        if (destLeft >= nbCol)
          throw new Exception("pb addmod")
      }
      (even, odd,moveTorify)
    }



  def prepareBit(mem: Array[Int]): Unit = {

      mem(first - 1) = mem(last) >>> (nbCol + 2) //we start by computing  the very first integer t[first-1]
      mem(last + 1) = mem(first) << (nbCol + 2) //and then the very last integer t[last+1]

       for (i <- first - 1 to last + 1)   mem(i) = propagateBitxand1(mem(i), nbCol, maskS) //avant on faisait pas le propagate sur la derniere ligne
    }
    override def isMirrorSafe(h: Array[Int]): Boolean = encodeLt.super.isMirorSafe(h)
    override def mirror(mem: Array[Int]): Unit = {
      val matBool=Array.ofDim[Boolean](nbLine,nbCol)
        mirrorifyFast(mem)
     //if (! isMirrorSafe(mem))   throw new Exception("miror not working") //la verif coute cher en temps, on la remet en cas de pb
  }
        override def torusify(mem: Array[Int]): Unit =  torusifyFast(mem)
    //else    throw new Exception("miror on non V")

    override def torusify(mem: Array[Array[Int]]): Unit =  mem.map(torusifyFast(_))


    //else   throw new Exception("miror on non V")
 /** do the copying part of mirroring in a simpe and safe but time expensive way*/
    def mirrorifySafe(mem: Array[Int]) = {
      val matBool=Array.ofDim[Boolean](nbLine,nbCol)
      decode(mem,matBool)
      miror(matBool)
      encode(matBool,mem)
    }


    /** applies a precomputed list of move, (distinct for even or odd int32. */
    def applyMove(v: Int, moves: Map[Int, Int], mask: Int): Int = {
      var res = v
      for (move <- moves)
        res = moveBitxtoy(res, move._1, move._2, mask)
      res
    }

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
    /** does the same as mirrorSafe, in a faster way, but much more complex.  */
    def mirrorifyFast(mem: Array[Int]) = {
      //mirror to top line
      val bout = 32 % (nbCol + 2)
      val maskFirst = maskCompact(nbCol) >>> bout //cover the first line. we pass over the first two bits, for nbCol+2=10
      val line2 = if (nbInt32 > 2) mem(4) else mem(first) << nbCol + 2 //faut aussi rotationner les bits eux meme
      val line2Trunc = line2 & maskFirst
      val line2rotated = (line2Trunc >>> 1 | (line2Trunc << (nbCol - 1))) & maskFirst
      mem(first) = writeInt32(mem(first), line2rotated, maskFirst) //copy line 2, to line 0
      //mirror to  bottom line
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
    def bprint(line:Int)=println(line.toBinaryString.reverse.padTo(32, '0').reverse.grouped(8).toList)
    def printBinary(mem: Array[Int])=for(line<-mem) bprint(line)
    private def torusifyFast(mem: Array[Int]) = {
      val bout = 32 % (nbCol + 2)
      val maskFirst = maskCompactTighter(nbCol) >>> bout //cover the first line. we pass over the first two bits, for nbCol+2=10
      val line1 = mem(first+1)//if (nbInt32 > 2) mem(4) else mem(first) << nbCol + 2 //faut aussi rotationner les bits eux meme
      val line1Trunc = line1 & maskFirst
      val nbrot:Int= (nbLine-1)/2
      val line1rotated = (line1Trunc << nbrot | (line1Trunc >>> (nbCol  - nbrot))) & maskFirst
      //torusify to last line
      val maskOffset = (nbLignePerInt32 - 1) * (nbCol + 2)
      val maskLast = maskFirst >>> maskOffset
      mem(last) = writeInt32(mem(last), line1rotated >>> maskOffset, maskLast) //copy line 1, to last line
      //torusify to first line
      val linem1 = mem(last - 1)
      val linem1Trunc = linem1 & maskLast //faut aussi rotationner les bits eux meme
      val linem1rotated = (linem1Trunc >>> nbrot | (linem1Trunc << (nbCol  - nbrot))) & maskLast //& 0x00000002
      mem(first) = writeInt32(mem(first), linem1rotated << maskOffset, maskFirst) //copy line m1, to line 0

      //process right and left column using precomputed  moves in movesEven and movesOdd
      val maskSlim = 1 //we will now have to move bit by bit, because the moves are not uniform across a given integers
      for (i <- first - 1 until last + 1) {
        val mv: Map[Int, Int] = shift(moveTorify, i / 2 - 1) //adds a shift i/2-1 to the move computed for the first line
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






