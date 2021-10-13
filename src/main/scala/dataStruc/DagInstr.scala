package dataStruc

import compiler.Circuit.{AstPred, TabSymb, iTabSymb}
import compiler.{AST, Affect, CallProc, InfoNbit, InfoType, Instr}
import compiler.AST.{isNotRead, rewriteAST2}
import scala.collection.immutable.HashSet
import scala.collection.{Iterable, immutable, mutable}
import DagInstr.setInputAndOutputNeighbor
import dataStruc.DagNode.paquets

object DagInstr {
  def apply(visitedL: List[Instr], dag: Dag[AST[_]] = null) = {
    val res = new DagInstr(List(), dag)
    res.imposeSchedule(visitedL)
    res
  }

  implicit def DagInstrtoDagInstr(d: Dag[Instr]): DagInstr = new DagInstr(d.allGenerators)

  /**
   *
   * @param instrs data to organize into a dag, using strings.
   *               it needs not be instructions
   *               only names and usedVar need to be defined
   * @tparam T
   * Compute inputNeighbor which defines a  Dag of instructions,
   * an input neighbor is an affectation which set a used variable
   * exept for an instruction of the form shifttoto=toto
   * which will be input neighbor to the instructionn defining toto
   * toto will be included in shsissfttoto's used var
   * it will be apperently scheduled later but in fact not because
   * ending up having a higher priority, let it be scheduled earlier
   * due to the specifics of our scheduling algorithm
   * * */

  def setInputNeighbor[T <: SetInput[T]](instrs: List[T]) = {
    /** map each variable to the instructions which define that variable */
    val defs = defby(instrs) //= immutable.HashMap.empty ++ instrs.flatMap(a => a.names.map(_ -> a)) //FIXME ne pas mettre les updates
    /** variable which are shifted **/
    val shifted: HashSet[String] = HashSet() ++ instrs.filter(_.isShift).flatMap(a => a.names).map(_.drop(5))
    for (instr <- instrs) {
      var usedVars = instr.usedVars
      //  if(instr.names.nonEmpty && shifted(instr.names(0))) usedVars=usedVars+("shift"+instr.names(0))//rajoute shiftToto dans usedVar ToTO
      if (instr.isShift) usedVars = usedVars + instr.names(0).drop(5) //rajoute Toto dans usedVar shiftToTO

      instr.inputNeighbors = List.empty[T] ++ usedVars.filter(defs.contains(_)).map(defs(_))
    }
  }

  def defby[T <: SetInput[T]](instrs: List[T]) = immutable.HashMap.empty ++ instrs.flatMap(a => a.names.map(_ -> a))

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
 * When the dag 's element are instructions,
 * new method can be added, such as the affectify method
 *
 * @param generators generators which are callProc in {memo, show, bug}.
 * @param dag        the underlying dag of AST, if available  */
class DagInstr(generators: List[Instr], private var dag: Dag[AST[_]] = null)
  extends Dag[Instr](generators) //reconstruct the whole Dag
    with DagSetInput[Instr] {
  def imposeSchedule(scheduled: List[Instr]) = {
    visitedL = scheduled.reverse
  }

  override def toString: String = visitedL.reverse.mkString("")

  def defby = DagInstr.defby(visitedL)

  /**
   * newly generated affect instructions. to be accessed later to complete the symbolTable, as nonGenerators
   */
  var newAffect: List[Affect[_]] = null

  /**
   *
   * @param toBeReplaced predicate true for AST node to be replaced
   * @return   new DagInstr,  by replacing toBeReplaced nodes
   *           *   by read expressions.
   *           usage:    1-  with dedagify, for each AST nodes used more than once
   *           2-   with procedurIfy, for expressions with head and tail, (e.isCoons)
   *           3-  with bitify, for effective data parameter in CallProc
   *           this will thus include system instructions such as memo or show
   *           - for memo it is not apropriate, because store could be directly made
   *           - neither is it for debug because we want to spare this computation
   *           - for show it is because displayed film are normally computed anyway
   *           and returning the array allows to avoid making tests all the time in the macro
   *           the test will be done a single time in the enclosing fun which is not a macro*
   ***/
  def affectIfy(toBeReplaced: AstPred): DagInstr = { //TODO faire un seul appel pour éviter de reconstuire le DAG plusieurs fois
    /** reads are removed from toBeReplaced to not generatre x=x */
    val toBeRepl: List[AST[_]] = dagAst.visitedL.filter(a => toBeReplaced(a) && isNotRead(a));

    toBeRepl.map(_.setNameIfNull());
    if (toSet(toBeRepl).size < toBeRepl.size) //since name are given by hand we check that no two names are equals
      throw new RuntimeException("a name is reused two times or we want to rewrite a read")
    val repr = represent
    val deDagRewrite: rewriteAST2 = (e: AST[_]) => e.treeIfy(toBeReplaced, repr)
    //val deDagRewrite: rewriteAST2 = (e: AST[_]) => e.treeIfy(toBeReplaced, repr)
    /** avoid generate e=read(e) when  the affected expression is itself rewritten recursively */
    val deDagExclude: AST[_] => AST[_] = (e: AST[_]) => e.treeIfy((e2: AST[_]) => (toBeReplaced(e2) && (e2 != e)), repr)

    /** rewrite recursviely the affect expression. we use this slightly modified dedagExclude instead of dedagRewrite
     * to not generatre x=x  */
    val affectExpList = toBeRepl.map(deDagExclude)

    /** returns the newly generated affect instruction */
    newAffect = affectExpList.map((e: AST[_]) => Affect(e.name, e))
    val rewrite: Instr => Instr = (i: Instr) => i.propagate(deDagRewrite)
    propagateUnit(rewrite, newAffect) //computes input and output neighbors
  }

  /**
   * @return set of AST which are used twice within those instruction to be replaced by an affectation
   *         we must also add up usage from callProc instruction
   */
  def inputTwice: collection.Set[AST[_]] = {
    val l: collection.Set[AST[_]] = dagAst.inputTwice(visitedL.flatMap(_.exps))
    //  print(l)
    l
  }


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
