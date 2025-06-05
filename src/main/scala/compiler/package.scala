import simulator.CAloops2

package object compiler {

  def rotateLeft[A](seq: Seq[A]): Seq[A] = {
    rotateLeft(seq, 1)
  }

  def rotateLeft[A](seq: Seq[A], i: Int): Seq[A] = {
    val size = seq.size
    val (first, last) = seq.splitAt(i % size)
    last ++ first
  }

  def rotateRight[A](seq: Seq[A], i: Int): Seq[A] = {
    val size = seq.size
    val (first, last) = seq.splitAt(size - (i % size))
    last ++ first
  }

  def rotateRight[A](seq: Seq[A]): Seq[A] = {
    rotateRight(seq, 1)
  }

  //Todo mettre ensemble et factoriser le ROT de ASTL
  def rotate[A](seq: Seq[A], dir: Boolean): Seq[A] = {
    if (dir) rotateRight(seq) else rotateLeft(seq)
  } //dir=True correspond to trigonometric order

  def printMem(m: Array[Int]) = {
    for (n <- 0 until m.length)
      System.out.println((m(n) | 0x80000000).toBinaryString)
    System.out.println("")
  }

  def printMem(v: Int) = {
    System.out.println((v | 0x80000000).toBinaryString)
    System.out.println("")
  }

  /**
   *
   * @param m int from which to read a bit
   * @param d position of the bit to read,  between 0 and 31
   * @return O or 1, depending if the bit to read was true or false
   */
  def getBitx(m: Int, d: Int) = m >>> d & 1

  /**
   *
   * @param m   m int on which to write a bit
   * @param d   position where to write, between 0 and 31
   * @param bit bit that should be written, either O or 1
   * @return m where bit at position d as bin set to bit
   */
  def putBitx(m: Int, d: Int, bit: Int): Int = {
    val mask = 1 << d; m & ~mask | bit << d
  }

  /**
   *
   * @param mem  copies an entire line   of mem into another entire line
   * @param src  source line
   * @param dest destination line
   */
  def copyEntireLine(mem: Array[Int], src: Int, dest: Int, nbIntPerLine: Int, nbLineCAp1: Int) = {
    for (j <- 0 until nbIntPerLine)
      mem(1 + dest + j * nbLineCAp1) = mem(1 + src + j * nbLineCAp1)
  }

  val maskReset0and32:Int= ~(1 | 1<<31)
  /** bit 0 and 31 are null at the start, but, as computation proceeds, they get values, and when rotate rignt or left is
   * aplied, before doing the shift << or >> followed by the 'OR' we must remove them */
  def reset0and31(i:Int):Int=i&maskReset0and32
  /**
   *
   * @param mem  memory of the CA
   * @param line index of line which should be rotated.
   */
  def rotateEntireLineRigt(mem: Array[Int], line: Int, nbIntPerLine: Int, nbLineCAp1: Int) = {
    val lastIndex = 1 + line + (nbIntPerLine - 1) * nbLineCAp1
    var previousFirstBit = mem(lastIndex) & 2 //the inital value of previousFirst can be random, the miror still work because of double miror on the corners.ppppppppp
    for (j <- 0 until nbIntPerLine) {
      val indexCur = 1 + line + j * nbLineCAp1
      val nextFirstbit = mem(indexCur) & 2 //save for the next iteration before mem(indexCur) is written
      mem(indexCur) = reset0and31(mem(indexCur) )>>> 1 | previousFirstBit << 29
      previousFirstBit = nextFirstbit
    }
  }
  def rotateEntireLineRigtOld(mem: Array[Int], line: Int, nbIntPerLine: Int, nbLineCAp1: Int) = {
    val lastIndex = 1 + line + (nbIntPerLine - 1) * nbLineCAp1 - 1
    var previousFirstBit = mem(lastIndex) & 2 //initial value
    for (j <- 0 until nbIntPerLine) {
      val indexCur = 1 + line + j * nbLineCAp1
      val nextFirstbit = mem(indexCur) & 2 //save for the next iteration before mem(indexCur) is written
      mem(indexCur) = mem(indexCur) >>> 1 | previousFirstBit << 29
      previousFirstBit = nextFirstbit
    }
  }

  /**
   *
   * @param mem  memory of the CA
   * @param line index of line which should be rotated.
   *  y a un bug la dedans
   */
  def rotateEntireLineLeft(mem: Array[Int], line: Int, nbIntPerLine: Int, nbLineCAp1: Int) = {
    val lastIndex = 1 + line //corresponds here ot the first considered index, because one because we go in other direction
    var previousLastBit = mem(lastIndex) & 1 << 30 //we take the bit before the strongest
    for (j <- (0 until nbIntPerLine).reverse) { //we start by the last
      val indexCur = 1 + line + j * nbLineCAp1
      val nextLastBit = mem(indexCur) & 1 << 30 //save for the next iteration before mem(indexCur) is written
      mem(indexCur) = reset0and31( mem(indexCur) )<< 1 | previousLastBit >>> 29
      previousLastBit = nextLastBit
    }
  }

  def rotateEntireLineLeftOld(mem: Array[Int], line: Int, nbIntPerLine: Int, nbLineCAp1: Int) = {
    val lastIndex = 1 + line //first one because we go in other direction
    var previousLastBit = mem(lastIndex) & 1 << 30 //we take the bit before the strongest
    for (j <- (0 until nbIntPerLine).reverse) { //we start by the last
      val indexCur = 1 + line + j * nbLineCAp1
      val nextLastBit = mem(indexCur) & 1 << 30 //save for the next iteration before mem(indexCur) is written
      mem(indexCur) = mem(indexCur) << 1 | previousLastBit >>> 29
      previousLastBit = nextLastBit
    }
  }

}
