package dataStruc

import compiler.Circuit.{AstPred, TabSymb, iTabSymb}
import compiler.{AST, Affect, CallProc, InfoNbit, InfoType, Instr, ProgData1}
import compiler.AST.{isNotRead, rewriteAST2}
import scala.collection.immutable.HashSet
import scala.collection.{Iterable, immutable, mutable}
import DagInstr.setInputAndOutputNeighbor
import dataStruc.DagNode.paquets

object DagInstr {
  implicit def DagInstrtoDagInstr(d: Dag[Instr]): DagInstr = new DagInstr(d.allGenerators)

  /** Compute the Dag of instructions, where a neighbor
   * is an affectation which set a used variable   */
  def setInputNeighbor[T <: SetInput[T]](instrs: List[T]) = {
    /** map each variable to the instructions which define that variable */
    val defby = immutable.HashMap.empty ++ instrs.flatMap(a => a.names.map(_ -> a)) //FIXME ne pas mettre les updates
    for (a <- instrs)
      a.inputNeighbors = List.empty[T] ++ a.usedVars.filter(defby.contains(_)).map(defby(_))
  }

  def setOutputNeighbors[T <: SetOutput[T]](instrs: List[T]) = {
    for (a <- instrs)
      for (b <- a.inputNeighbors)
        b.outputNeighbors = a :: b.outputNeighbors;
  }

  /** Compute  input neighbor of instruction $i$ as affectation which set a  variables used by $i$ */
  def setInputAndOutputNeighbor[T <: SetOutput[T]](instrs: List[T]) = {
    setInputNeighbor(instrs)
    setOutputNeighbors(instrs)
  }
}

/**
 * When the dag 's element are instructions, the affectify method can be defined
 *
 * @param generators generators which are callProc in {memo, show, bug}.
 * @param dag        the underlying dag of AST, if available  */
class DagInstr(generators: List[Instr], private var dag: Dag[AST[_]] = null)
  extends Dag[Instr](generators) //reconstruct the whole Dag
    with DagSetInput[Instr] {
  override def toString: String = visitedL.reverse.mkString("")

  /**
   * newly generated affect instructions. to be accessed later to complete the symbolTable, as nonGenerators
   */
  var newAffect: List[Affect[_]] = null

  /**
   *
   * @param toBeReplaced predicate true for AST node to be replaced
   * @return new DagInstr,  by replacing toBeReplaced nodes
   *         *   by read expressions.
   *         usage:    1-  with dedagify, for each AST nodes used more than once
   *         2-   with procedurIfy, for expressions with head and tail, (e.isCoons)
   *         3-  for effectiive data parameter in CallProc
   *         *
   **/
  def affectIfy(toBeReplaced: AstPred): DagInstr = {
    /** reads are removed from toBeRepl to not generatre x=x */
    val toBeRepl: List[AST[_]] = dagAst.visitedL.filter(a => toBeReplaced(a) && isNotRead(a));

    toBeRepl.map(_.setNameIfNull());
    if (toSet(toBeRepl).size < toBeRepl.size) //since name are given by hand we check that no two names are equals
      throw new RuntimeException("a name is reused two times")
    val repr = represent
    val deDagRewrite: rewriteAST2 = (e: AST[_]) => e.treeIfy(toBeReplaced, repr)
    /** avoid generate e=read(e) when rewrite recursively the affected expression */
    val deDagExclude = (e: AST[_]) => e.treeIfy((e2: AST[_]) => (toBeReplaced(e2) && (e2 != e)), repr)

    /** rewrite recursviely the affect expression. we use this slightly modified dedagExclude instead of dedagRewrite
     * to not generatre x=x  */
    val affectExpList = toBeRepl.map(deDagExclude)

    /** the newly generated affect instruction */
    newAffect = affectExpList.map((e: AST[_]) => Affect(e.name, e))
    val rewrite: Instr => Instr = (i: Instr) => i.propagate(deDagRewrite)
    propagateUnit(rewrite, newAffect)
  }

  /**
   * @return set of AST which are used twice within those instruction to be replaced by an affectation
   *         we must also add up usage from callProc instruction
   */
  def inputTwice =
    dagAst.inputTwice(visitedL.flatMap(_.exps))


  /**
   * underlying dag of AST. if needed, and not computed, recompute it. */
  def dagAst: Dag[AST[_]] = {
    if (dag == null) dag = new Dag(visitedL.flatMap(i => i.exps));
    dag
  }

  /**
   * @return returns a unique  name for each AST,
   *         necessary because distinct AST can be equals  when compared as case class hierarchie
   *         tries to find real name instead of created name with "aux_"
   *         For this purpose, visite the expression of the instructions, for they can differ.
   */
  private def represent: Map[AST[_], String] = {
    def bestof2Name(s: String, s2: String): String = {
      val i = 1; if (s.startsWith("_aux")) s2 else s
    }

    var bestName = immutable.HashMap.empty[AST[_], String]

    def newName(x: AST[_]) =
      if (!bestName.contains(x))
        x.name
      else bestof2Name(bestName(x), x.name)

    for (instr <- visitedL) for (x <- instr.exps) bestName += (x -> newName(x)) //on récupére des noms!!
    for (x <- dagAst.visitedL) bestName += (x -> newName(x))
    bestName
    // immutable.HashMap.empty[AST[_], AST[_]] ++ dagAst.visitedL.map(x => x -> x)
  }
}
