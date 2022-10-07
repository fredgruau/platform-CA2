package dataStruc

import compiler.Circuit.{TabSymb, iTabSymb}
import compiler.{AST, ASTBt, Affect, CallProc, InfoNbit, InfoType, Instr}
import compiler.AST.{AstPred, Call1, Read, isNotRead, rewriteAST2}

import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.{Iterable, immutable, mutable}

object DagInstr {
  /**
   *
   * @param visitedL list of instructions, we want to make a dag of
   * @param dag      the instructions expressions node, not obligatory can be specified as null, and will be recompiled if needed
   * @return the dag is constructed, with the schedule preserved as supplied,
   *         (that would not be the case if we were giving only generators
   *         however, we loose the generators. Allgenerators is empty, so we should no longer use it to reconstruct the dag.
   */
  def apply(visitedL: List[Instr], dag: Dag[AST[_]] = null) = {
    val res = new DagInstr(List(), dag)
    res.imposeSchedule(visitedL)
    res
  }

  implicit def DagInstrtoDagInstr(d: Dag[Instr]): DagInstr = new DagInstr(d.allGenerators)



}

/**
 * When the dag 's element are instructions,
 * new method can be added, mainly the affectify method
 * an implicit transformation allows to turn a dag into a dagInstr, when  needed.
 *
 * @param generators generators which are callProc in {memo, show, bug}.
 * @param dag        the underlying dag of AST, if available
 *                   todo we should distinguish the case of the DAGinstr whose schedule should be maintained; for those, we cannot recontruct visitedL from the generators, the schedule would be lost.
 *
 *
 **/
class DagInstr(generators: List[Instr], private var dag: Dag[AST[_]] = null)
  extends Dag[Instr](generators) //reconstruct the whole Dag
    with DagWired[Instr] {

  def imposeSchedule(scheduled: List[Instr]) = {
    visitedL = scheduled.reverse
  }

  override def toString: String = "there is " + visitedL.length + " instructions\n" +
    visitedL.reverse.map((i: Instr) => i.toString() + "\n").mkString("")

  //def defby = DagInstr.defby(visitedL)

  def defby = WiredInOut.defby(visitedL)

  /**
   * newly generated affect instructions. to be accessed later to complete the symbolTable, as nonGenerators
   * in topological order, from greater to lower, apply reverse in order to process.
   */
  var newAffect: List[Affect[_]] = null

  /**
   *
   * @param toBeReplaced    predicate true for AST node to be replaced
   * @param scheduleMatters true is schedule must be preserved
   * @return   new DagInstr,  by replacing toBeReplaced nodes by read nodes.
   *           usage:    1-  with treeify, for each AST nodes used more than once
   *           2-   with procedurIfy, for expressions with head and tail, (e.isCoons)
   *           3-  with bitify, for effective data parameter in CallProc
   *           4- for system call such as memo bugif or show
   *           - for memo it is not apropriate, because store could be directly made
   *           - neither is it for bugif because we want to be able to spare this computation
   *           - for show it may be apropriate because displayed fields are normally computed anyway
   *           using a variable allows to test  a single time wether to display or not,  for fields with arity > 1
   *           we use the following prefix:
   *           auxL pour Locus
   *           auxC pour coons
   *           auxB pour Bitify (could not identify occurence)
   *           auxO pour redop
   *           auxM pour macroisation
   *           there is 10 instructions
   ***/
  def affectIfy(toBeReplaced: AstPred, prefix: String, scheduleMatters: Boolean = false): DagInstr = { //TODO faire un seul appel pour éviter de reconstuire le DAG plusieurs fois
    /** reads have already been removed from toBeReplaced to not generate x=x */
    if (!scheduleMatters && allGenerators.isEmpty)
      throw new Exception("if no schedule then dag is reconstructed from generator which should not be empty")
    val toBeAffected: List[AST[_]] = dagAst.visitedL.filter(a => toBeReplaced(a) /*&& isNotRead(a)*/);
    if (toBeAffected.filter(AST.isRead(_)).nonEmpty)
      if (false) //treeIfyParam does affect read, that is not cool
      throw new Exception("we try to affectize read, that would generate silly cycles")
    toBeAffected.map(_.setNameIfNull(prefix));
    if (toSet(toBeAffected).size < toBeAffected.size) //since name are given manually we need to check that  names are distincts
    throw new RuntimeException("a name is reused two times or we want to rewrite a read")
    /** associate a unique id for each affectation that will be generated */
    val repr: Map[AST[_], String] = represent(toBeAffected)

    val deDagRewrite: rewriteAST2 = (e: AST[_]) => e.setReadNode(toBeReplaced, repr)
    /** avoid generating x=x when  the affected expression is itself rewritten recursively */
    val deDagExclude: rewriteAST2 = (e: AST[_]) => e.setReadNode((e2: AST[_]) => (toBeReplaced(e2) && (e2 != e)), repr)
    /** rewrite recursviely the affect expression so as to insert read in them where necessary.  */
    val affectExpList: List[AST[_]] = toBeAffected.map(deDagExclude)

    /** newly generated affectations */
    newAffect = affectExpList.map((e: AST[_]) => Affect(e.name, e))
    val rewrite: Instr => Instr = (i: Instr) => i.propagate(deDagRewrite) //replace the expression by a read(identifier)
    if (scheduleMatters) {
      propagateUnitKeepSchedule(rewrite, newAffect); dag = null; this
    } //dagdag should be recomputed because the expressions have changed
    else propagateUnitKeepGenerators(rewrite, newAffect) //computes input and output neighbors


  }


  /**
   *
   * @param tm1s expression argument to a Tm1, they should be affectified and inserted at the right place which after
   *             the affectation that uses it and also after its reads are computed.
   * @return
   */
  def affectizeTm1(tm1s: List[ASTBt[_]]): DagInstr = { //TODO faire un seul appel pour éviter de reconstuire le DAG plusieurs fois
    tm1s.map(_.setNameIfNull("tmun")); //creates new registers
    //  toBeRepl.map(_.forwardName()) //that's because we will remove tm1
    val repr = represent(tm1s) //2(toBeRepl)
    val deDagRewrite: rewriteAST2 = (e: AST[_]) => e.setReadNode(tm1s.toSet.asInstanceOf[Set[AST[_]]], repr) //replaces tm1s by read
    /** avoid generate e=read(e) when  the affected expression is itself rewritten recursively */
    val deDagExclude: AST[_] => AST[_] = (e: AST[_]) => e.setReadNode((e2: AST[_]) => (tm1s.toSet(e2.asInstanceOf[ASTBt[_]]) && (e2 != e)), repr)
    /** rewrite recursively the affect expression. we use this slightly modified dedagExclude instead of dedagRewrite
     * to not generatre x=x  */
    val affectExpList: List[AST[_]] = tm1s.map(deDagExclude).toList

    /** returns the newly generated affect instruction */
    newAffect = affectExpList.map((e: AST[_]) => Affect(e.name, e.asInstanceOf[ASTBt[_]].detm1ise))
    val rewrite: Instr => Instr = (i: Instr) => i.propagate(deDagRewrite)
    propagateUnit3(rewrite, newAffect);
    this
  }


  /**
   * @return set of AST which are used twice within those instruction to be replaced by an affectation
   *         we must also add up usage from callProc instruction
   */
  def inputTwice: collection.Set[AST[_]] = dagAst.inputTwice(visitedL.flatMap(_.exps))


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
   * @param newExp expressions needing a name
   * @return a map associating a unique  name
   *         distinct AST can be equals  when compared as case class hierarchy,
   *         hence the necessity of a key to remove ambiguity
   *         The algo tries to find real name instead of created name with "aux_"
   */
  private def represent(newExp: List[AST[_]]): Map[AST[_], String] = {
    /**
     * @param s1 option 1
     * @param s2 option 2
     * @return best option
     */
    def bestof2Name(s1: String, s2: String): String = {
      val i = 1;
      if (s1.startsWith("_aux")) s2 else s1
    }

    /** record the best name find up till now for a given AST expression */
    var bestName = immutable.HashMap.empty[AST[_], String]

    /**
     * update the the best name find up till now for a given AST expression
     *
     * @param x new AST to be named
     * @return new best name
     */
    def newName(x: AST[_]) = {
      if (x.name.startsWith("shift")) throw new Exception("shift is a reserved prefix, do not use it please")
      if (x.name.startsWith("ll")) throw new Exception("ll is a reserved prefix, do not use it please")
      if (!bestName.contains(x)) x.name
      else bestof2Name(bestName(x), x.name)
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

    for (x <- newExp) if (x.name != null) bestName += (x -> newName(x))
    checkDistinctName(bestName);
    bestName
  }

}
