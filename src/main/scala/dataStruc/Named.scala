package dataStruc

import compiler.AST

import scala.collection.mutable

object Named {
  private var nameCompteur: Int = 0

  def getCompteur: Int = {
    nameCompteur += 1;
    nameCompteur
  }

  private var doNotUse = scala.collection.mutable.Set[String]()

  def doNotUseForName(s: Seq[String]): mutable.Set[String] = {
    doNotUse ++= s
  }

  def OkToUseForName(s: String): Boolean = !doNotUse.contains(s);
  {
    doNotUseForName(List("arg", "arg2"))
  }
}

trait Named {
  var name: String = _;

  def setName(value: String) {
    name = value
  }

  /** generates a unique name starting by "aux" for AST which do not a name yet  */
  def setNameIfNull() = {
    if (name == null) name = "_aux" + Named.getCompteur
  }

  def addAfter(value: String) {
    name = name + value
  };

  def addBefore(value: String) {
    name = value + name
  }
}