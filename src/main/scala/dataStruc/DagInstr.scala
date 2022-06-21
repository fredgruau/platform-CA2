package dataStruc

import compiler.Circuit.{AstPred, TabSymb, iTabSymb}
import compiler.{AST, ASTBt, Affect, CallProc, CodeGen, InfoNbit, InfoType, Instr}
import compiler.AST.{Call1, Read, isNotRead, rewriteAST2}

import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.{Iterable, immutable, mutable}

object DagInstr {
  def apply(visitedL: List[Instr], dag: Dag[AST[_]] = null) = {
    val res = new DagInstr(List(), dag)
    res.imposeSchedule(visitedL)
    res
  }

  implicit def DagInstrtoDagInstr(d: Dag[Instr]): DagInstr = new DagInstr(d.allGenerators)



}

/**
 * When the dag 's element are instructions,
 * new method can be added, such as the affectify method
 *
 * @param generators generators which are callProc in {memo, show, bug}.
 * @param dag        the underlying dag of AST, if available
 *                   todo we should distinguish the case of the DAGinstr whose schedule should be maintained; for those, we cannot recontruct visitedL from the generators, the schedule would be lost.
 *
 *
 **/
class DagInstr(generators: List[Instr], private var dag: Dag[AST[_]] = null)
  extends Dag[Instr](generators) //reconstruct the whole Dag
    with DagOutputUnion[Instr] {

  def imposeSchedule(scheduled: List[Instr]) = {
    visitedL = scheduled.reverse
  }

  override def toString: String = visitedL.reverse.mkString("")

  //def defby = DagInstr.defby(visitedL)
  def defby = Dag.defby3(visitedL)

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
  def affectIfy(toBeReplaced: AstPred, dagdag: Boolean = true): DagInstr = { //TODO faire un seul appel pour éviter de reconstuire le DAG plusieurs fois
    /** reads are removed from toBeReplaced to not generatre x=x */
    val toBeRepl: List[AST[_]] = dagAst.visitedL.filter(a => toBeReplaced(a) /*&& isNotRead(a)*/);
    toBeRepl.map(_.setNameIfNull());

    if (toSet(toBeRepl).size < toBeRepl.size) //since name are given by hand we check that no two names are equals
    throw new RuntimeException("a name is reused two times or we want to rewrite a read")
    val repr = represent(toBeRepl)

    val deDagRewrite: rewriteAST2 = (e: AST[_]) => e.preTreeIfy(toBeReplaced, repr)
    /** avoid generate e=read(e) when  the affected expression is itself rewritten recursively */
    val deDagExclude: AST[_] => AST[_] = (e: AST[_]) => e.preTreeIfy((e2: AST[_]) => (toBeReplaced(e2) && (e2 != e)), repr)
    /** rewrite recursviely the affect expression so   as to insert read in them if necessary. we use this slightly modified dedagExclude instead of dedagRewrite
     * to not generatre x=x  */
    val affectExpList: List[AST[_]] = toBeRepl.map(deDagExclude)

    /** returns the newly generated affect instruction */
    newAffect = affectExpList.map((e: AST[_]) => Affect(e.name, e))
    val rewrite: Instr => Instr = (i: Instr) => i.propagate(deDagRewrite) //replace the expression by a read(identifier)
    if (dagdag) propagateUnit(rewrite, newAffect) //computes input and output neighbors
    else {
      propagateUnit2(rewrite, newAffect);
      dag = null; //should be recomputed because the expressions have changed
      this
    }
  }


  /**
   *
   * @param toBeRepl expression argument to a Tm1, they should be affectified and inserted at the right place which after
   *                 the affectation that uses it and also after its reads are computed.
   * @return
   */
  def deTm1fy(toBeRepl: Set[ASTBt[_]]): DagInstr = { //TODO faire un seul appel pour éviter de reconstuire le DAG plusieurs fois
    toBeRepl.map(_.setNameTm1());
    //  toBeRepl.map(_.forwardName()) //that's because we will remove tm1
    val repr = represent(toBeRepl.toList) //2(toBeRepl)
    val deDagRewrite: rewriteAST2 = (e: AST[_]) => e.preTreeIfy(toBeRepl.asInstanceOf[Set[AST[_]]], repr)
    /** avoid generate e=read(e) when  the affected expression is itself rewritten recursively */
    val deDagExclude: AST[_] => AST[_] = (e: AST[_]) => e.preTreeIfy((e2: AST[_]) => (toBeRepl(e2.asInstanceOf[ASTBt[_]]) && (e2 != e)), repr)
    /** rewrite recursively the affect expression. we use this slightly modified dedagExclude instead of dedagRewrite
     * to not generatre x=x  */
    val affectExpList: List[AST[_]] = toBeRepl.map(deDagExclude).toList

    /** returns the newly generated affect instruction */
    newAffect = affectExpList.map((e: AST[_]) => Affect(e.name, e.asInstanceOf[ASTBt[_]].detm1ise))
    val rewrite: Instr => Instr = (i: Instr) => i.propagate(deDagRewrite)
    propagateUnit3(rewrite, newAffect); //not apropriate
    this
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

  /** returns instructions defining a variable used once */
  def usedOnce(): List[Instr] = {
    def intermReduce(str: String): Boolean = str.contains('#')

    def isShift(str: String): Boolean = str.startsWith("shift")

    def nbRead(value: AST[_], str: String): Int = value match {
      case Read(x) => if (x == str) 1 else 0
      //case Call1(_,exp)=>
      case _ =>
        val v1 = value.inputNeighbors.map(nbRead(_, str))
        val v = v1.reduceLeft(_ + _)
        v
    }

    val usedByOnce = visitedL.filter(_.outputNeighbors.size == 1) //we first select id which are used by a single instruction
    val usedByOnceNoDiese = usedByOnce.filter((f: Instr) => !(intermReduce(f.names(0))) && !isShift((f.names(0))))

    val u = usedByOnce.filter((a: Instr) => nbRead(a.outputNeighbors.head.exps(0), a.names(0)) == 1) //we then check that this instruction uses them once
    u
  }


  /**
   * underlying dag of AST. if needed, and not computed, recompute it. */
  def dagAst: Dag[AST[_]] = {
    if (dag == null)
      dag = new Dag(visitedL.flatMap(i => i.exps));
    dag
  }

  /**
   * @return returns a unique  name for each AST,
   *         necessary because distinct AST can be equals  when compared as case class hierarchie
   *         generate silly names systematically.
   */
  private def represent2(newExp: List[AST[_]]): Map[AST[_], String] = {
    val res: HashMap[AST[_], String] = HashMap.empty ++ newExp.map((e: AST[_]) => (e -> e.name))
    res
  }

  /** verifies that distinct trees get distinct names */
  def checkDistinctName(bestName: HashMap[AST[_], String]) = {
    if (bestName.values.toSet.size < bestName.keys.toSet.size) {
      for ((x, y) <- bestName)
        println(y + " is the name of " + x.toStringTree)
      println("______________________________________________________________________________________________________________")
      throw new Exception("there are distinct trees with identical names, " +
        "probably due to over agressing search for meaningfull names," +
        "complete the list of forbidden names in OkToUseForName in named.scala"
      )
    }
  }

  /**
   * @return returns a unique  name for each AST, and subAst, for which a name exists.
   *         necessary because distinct AST can be equals  when compared as case class hierarchie
   *         tries to find real name instead of created name with "aux_"
   *         For this purpose, visite the expression of the instructions, for they can differ.
   */
  private def represent(newExp: List[AST[_]]): Map[AST[_], String] = {
    /**
     * selects the best name between two options
     *
     * @param s1 option 1
     * @param s2 option 2
     * @return best option
     */
    def bestof2Name(s1: String, s2: String): String = {
      val i = 1;
      if (s1.startsWith("_aux")) s2 else s1
    }

    /**
     * record the best name find up till now for a given AST expression
     */
    var bestName = immutable.HashMap.empty[AST[_], String]

    /**
     * update the the best name find up till now for a given AST expression
     *
     * @param x new candidate name
     * @return new best name
     */
    def newName(x: AST[_]) = {
      if (x.name.startsWith("shift")) throw new Exception("shift is a reserved prefix, do not use it please")
      if (x.name.startsWith("ll")) throw new Exception("ll is a reserved prefix, do not use it please")
      if (!bestName.contains(x))
        x.name
      else bestof2Name(bestName(x), x.name)
    }

    for (x <- newExp)
      if (x.name != null)
        bestName += (x -> newName(x))
    /* for (instr <- visitedL)
       for (x <- instr.exps)
         if (x.name != null)
           bestName += (x -> newName(x)) //on récupére des noms!!
     for (x <- dagAst.visitedL)
       if (x.name != null)
         bestName += (x -> newName(x))*/
    checkDistinctName(bestName)
    bestName
  }



}
