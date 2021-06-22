package dataStruc

import compiler.Circuit.{AstPred, TabSymb, iTabSymb}
import compiler.{AST, Affect, CallProc, InfoNbit, InfoType, Instr, ProgData1}
import compiler.AST.{isNotRead, rewriteAST2}

import scala.collection.immutable.HashSet
import scala.collection.{Iterable, immutable, mutable}
import DagInstr.setInputNeighbor2
import dataStruc.DagNode.paquets

object DagInstr {
  implicit def DagInstrtoDagInstr(d: Dag[Instr]): DagInstr = new DagInstr(d.allGenerators)

  /** Compute the Dag of instructions, where a neighbor . an affectation which set a used variables   */
  def setInputNeighbor2[T <: SetInput[T]](instrs: List[T]) = {
    /** map each variable to the instructions which define that variable */
    val defby = immutable.HashMap.empty ++ instrs.flatMap(a => a.names.map(_ -> a)) //FIXME ne pas mettre les updates
    for (a <- instrs) {
      a.inputNeighbors = List.empty[T] ++ a.usedVars.filter(defby.contains(_)).map(defby(_))
      for (b <- a.inputNeighbors) b match {
        case c: SetOutput[T] => c.outputNeighbors = a :: c.outputNeighbors;
        case _ => ;
      }
    }

  }

  /** Compute the Dag of instructions, where a neighbor. an affectation which set a used variable   */
  def setInputNeighbor(instrs: List[Instr]) = {
    /** map each variable to the instructions which define that variable */
    val defby = immutable.HashMap.empty ++ instrs.flatMap(a => a.names.map(_ -> a)) //FIXME ne pas mettre les updates
    for (a <- instrs) a.inputNeighbors = List.empty[Instr] ++ a.usedVars.filter(v => defby.contains(v)).map(defby(_))
  }

}

/**
 * @param generators inital set of generators, system instruction callProc in {return dispaly debug}.
 */
class DagInstr(generators: List[Instr], private var dag: Dag[AST[_]] = null) extends Dag[Instr](generators) with DagSetInput[Instr] {
  override def toString: String = visitedL.reverse.mkString("")

  /**
   * newly generated affect instructions. to be accessed later to complete the symbolTable, as nonGenerators
   */
  var newAffect: List[Affect[_]] = null

  /**
   * @param whereReplaced
   * @return Rewrites all the DAG's node.  AST nodes for which "whereReplaced" is true are replaced by Affect Instructions
   *         It will be used
   *         1-  for each AST nodes used more than once
   *         2-  for expressions with head and tail, (e.isCoons)   For procedurIfy
   *         3-  for data parameter in CallProc */
  def affectIfy(whereReplaced: AstPred): DagInstr = {
    /** AST which need to be replaced, reads are removed to not generatre x=x */
    val toBeRepl: List[AST[_]] = dagAst.visitedL.filter(a => whereReplaced(a) && isNotRead(a));
    toBeRepl.map(_.setNameIfNull());
    if (toSet(toBeRepl).size < toBeRepl.size)
      throw new RuntimeException("a name is reused two times") //since name are given by hand we check that no two names are equals
    val repr = represent
    val deDagRewrite: rewriteAST2 = (e: AST[_]) => e.deDag((e2: AST[_]) => (whereReplaced(e2)), repr)
    /** avoid generate e=read(e) when rewrite recursively the affected expression */
    val deDagExclude = (e: AST[_]) => e.deDag((e2: AST[_]) => (whereReplaced(e2) && (e2 != e)), repr)
    /** rewrite recursviely the affect expression. we use this slightly modified dedagExclude instead of dedagRewrite  to not generatre x=x  */
    val affectExpList = toBeRepl.map(deDagExclude)

    /** the newly generated affect instruction */
    newAffect = affectExpList.map((e: AST[_]) => Affect(e.name, e))
    val rewrite: Instr => Instr = (i: Instr) => i.propagate(deDagRewrite)
    propagateUnit(rewrite, newAffect)
  }

  /**
   * @return the set of AST which are used twice, and will be replaced by an affectation
   */
  def usedTwice: Set[AST[_]] = {
    val users2 = visitedL.flatMap(_.exps)
    val nUser2 = immutable.HashMap.empty[AST[_], Int] ++ (dagAst.visitedL.flatMap(_.inputNeighbors) ++ users2).groupBy(identity).map { case (k, v) ⇒ k -> v.size }
    toSet(dagAst.visitedL.filter(e => nUser2.contains(e) && nUser2(e) > 1))
  }

  /** If dagAst is needed, and not computed, recompute it. */
  def dagAst: Dag[AST[_]] = {
    if (dag == null) dag = new Dag(visitedL.flatMap(i => i.exps)); dag
  }

  /**
   * @return returns a unique  name for each AST, necessary because distinct AST can be equals  when compared as case class hierarchie
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
