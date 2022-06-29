package compiler

/**
 *
 * used to compute a string encoding the locus,and Ring at compile time. needs to be covariant, so that AST can also be.
 *
 * @param name
 * @tparam L
 */


class repr[+L](val name: L)

object repr {
  def apply(a:Any)=new repr(a)
  implicit val nomV: repr[V] = new repr[V](V()); implicit val nomE: repr[E] = new repr[E](E()); implicit val nomF: repr[F] = new repr[F](F())

  implicit def nomT[L1 <: S, L2 <: S](implicit m1: repr[L1], m2: repr[L2]): repr[T[L1, L2]] = new repr[T[L1, L2]](T(m1.name, m2.name))

  implicit def nomCons[T1, T2](implicit m1: repr[T1], m2: repr[T2]): repr[(T1, T2)] = new repr[(T1, T2)]((m1.name, m2.name))

  implicit def nomLR[L <: Locus, R <: Ring](implicit m1: repr[L], m2: repr[R]): repr[(L, R)] = new repr[(L, R)]((m1.name, m2.name))
  def lpart[L <: Locus, R <: Ring](n: repr[(L, R)]): repr[L] = new repr[L](n.name._1)
  def rpart[L <: Locus, R <: Ring](n: repr[(L, R)]): repr[R] = new repr[R](n.name._2)
  implicit val nomB: repr[B] = new repr[B](B())
  implicit val nomR: repr[Ring] = new repr[Ring](new Ring())
  implicit val nomSI: repr[SI] = new repr[SI](SI())
  implicit val nomUI: repr[UI] = new repr[UI](UI())
 implicit val nomUISI: repr[UISI] = new repr[UISI](UISI()); //nomI is not declared  as implicit, otherwise it would offer ambiguous implicit values.
 implicit val nomUISIB: repr[UISIB] = new repr[UISIB](UISIB()); //nomI is not declared  as implicit, otherwise it would offer ambiguous implicit values.
 implicit val nomToto: repr[Int] = new repr[Int](33); //used when we do not care anymore.
}

class CentralSym[S2, S1, S2new]

object CentralSym {
  implicit val vEv: CentralSym[V, E, V] = new CentralSym[V, E, V]; implicit val fEf: CentralSym[F, E, F] = new CentralSym[F, E, F]
  implicit val vFe: CentralSym[V, F, E] = new CentralSym[V, F, E]; implicit val eFv: CentralSym[E, F, V] = new CentralSym[E, F, V]
  implicit val eVe: CentralSym[E,V,E] = new CentralSym[E,V,E]; implicit val fVf: CentralSym[F, V, F ] = new CentralSym[F,V,F]
}

class Red2[S1, S2, S3]

object Red2 {
  implicit val VEF: Red2[V, E, F] = new Red2[V, E, F]
}

