package compiler

sealed class Ring //j'appelle cela Ring parceque ca a une structure d'anneau avec or et and.
class I extends Ring //le type entier n'etends pas boolean, car OR,AND,XOR ne sont pas defini pour les entiers.
final case class B() extends Ring //le type boolean
final case class UI() extends I //unsigned int
final case class SI() extends I //signed int

/** used for boolean function that have the same code for either UI or SI. */
final case class UISI() extends I //both signe and unsigned

/** used for boolean function that have the same code for either UI or SI or Boolean??. */
final case class UISIB() extends Ring
