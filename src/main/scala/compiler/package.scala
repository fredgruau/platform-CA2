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

}
