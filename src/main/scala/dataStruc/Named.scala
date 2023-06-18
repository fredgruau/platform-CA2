package dataStruc

import compiler.AST

import scala.collection.immutable.HashMap
import scala.collection.{immutable, mutable}

object Named {
  def lify(s: String): String = "ll" + s

  def pify(s: String): String = "p" + s

  def isLayer(s: String): Boolean = s.charAt(0) == 'l' && s.charAt(1) == 'l'


  private var compteurAux: Int = 0
  private var nameCompteur2: Int = 0
  private var nameCompteur3: Int = 0

  /**
   * contains different counters
   */
  private var compteurs: immutable.HashMap[String, Int] = HashMap()

  def isTmp(s: String) = s.startsWith("_t")


  /**
   *
   * @param prefix name of compteur
   * @return string obtained by appending integer to prefix, after having incremented counter
   */
  def getCompteur(prefix: String): Int = {
    if (compteurs.contains(prefix)) compteurs = compteurs + (prefix -> (compteurs(prefix) + 1))
    else compteurs = compteurs + (prefix -> 0)
    compteurs(prefix)
  }

  def getCompteurAux: Int = {
    compteurAux += 1;
    compteurAux
  }

  def getCompteur2: Int = {
    nameCompteur2 += 1;
    nameCompteur2
  }

  def getCompteur3: Int = {
    nameCompteur3 += 1;
    nameCompteur3
  }

  private var doNotUse = scala.collection.mutable.Set[String]()

  def doNotUseForName(s: Seq[String]): mutable.Set[String] = {
    doNotUse ++= s
  }

  def OkToUseForName(s: String): Boolean = !doNotUse.contains(s);
  {
    //p1 is the name of the variable used for the parameter in funDef1, fuck it.
    doNotUseForName(List("arg", "arg2", "body", "op", "p1", "p2", "p3", "p4"))
  }
}

trait Named {
  var name: String = _;

  def setName(value: String) {
    name = value
  }

  def lify() = name = "ll" + name

  def pify() = name = "p" + name

  def isLayer: Boolean = name != null && name.charAt(0) == 'l' && name.charAt(1) == 'l'


  /**
   * generates a unique name starting by prefix for AST which do not a name yet
   *
   * @param prefix
   */
  def setNameIfNull(prefix: String) = {
    def twoDigit(s: String) = if (s.length == 1) "0" + s else s

    if (name == null) name = prefix + twoDigit("" + Named.getCompteur(prefix))
  }


  def addAfter(value: String) {
    name = name + value
  };

  def addBefore(value: String) {
    name = value + name
  }
}

