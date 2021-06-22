package compiler
import dataStruc.DagInstr.setInputNeighbor
import compiler.AST._
import compiler.Circuit._
import compiler.VarKind._
import dataStruc.DagNode._
import dataStruc.{Dag, DagInstr, Name}
import scala.collection._
import scala.language.postfixOps


object ProgData {
  def apply[T](f: Fundef[T], repl: iAstField[AST[_]] = immutable.HashMap.empty): ProgData[_] = {
    val (computeNodes, _) = getGreater(
      f.body :: repl.values.toList,
      immutable.HashSet.empty[AST[_]] ++ repl.keys) //those are passed so as not to be visited.
    val allNodes: List[AST[_]] = computeNodes ::: repl.keys.toList //the keys have not been visited, so we must explicitely add them into all nodes.
    Name.setName(f, ""); //for ''grad'' to appear as a name, it should be a field of an object extending the fundef.
    val funs: iTabSymb[Fundef[_]] = immutable.HashMap.empty ++ computeNodes.collect { case l: Call[_] => (l.f.namef, l.f) }
    new ProgData[T](f, funs.map { case (k, v) ⇒ k -> ProgData(v) }, allNodes)
  }
}





/**
 * Retrieves all the compute nodes associated to a function
 * @param f the function,
 * @param funs functions decomposing the code in a modular way
 * @param allNodes all the AST nodes, we'd like to put a DAG of AST instead.
 */
//noinspection ScalaUnnecessaryParentheses,ScalaUnnecessaryParentheses,ScalaUnnecessaryParentheses,ScalaUnnecessaryParentheses
class ProgData[+T](val f: Fundef[T], val funs: iTabSymb[ProgData[_]], val allNodes: List[AST[_]]) {

  /**
   * transform the DAG into a list of trees, adding a read node using names, and building  a list  of affect instruction.
   *  also does Substitution which is usefull only for the main body, the
   *     @param replaced   substitution map
   */
  def deDagise(replaced: iAstField[AST[_]] = immutable.HashMap.empty): ProgData1[T] = {
    val instrs = allNodes.flatMap(_.sysInstrs)
    val represent = immutable.HashMap.empty[AST[_], AST[_]] ++ allNodes.map(x => x -> x) //necessary because distinct AST can be equals  when compared as case class hierarchie
     val invertReplaced = replaced.map { _.swap }; //whenever the value is used, we need to count 1 for the key, so we compute the invertReplace map
    val users = f.body :: instrs.map(_.exp) //instruction using exp needs to be considered as users of exp also
    val nUser = immutable.HashMap.empty[AST[_], Int] ++ (allNodes.flatMap(_.inputNeighbors) ++ users).map(l => invertReplaced.getOrElse(l, l))
      .groupBy(identity).map { case (k, v) ⇒ k -> v.size }
    val usedTwice = allNodes.filter(e => nUser.contains(e) && nUser(e) > 1)
    // for (e <- usedTwice /**  ++ allNodes*/ ) e.checkName() //donne un nom. -- TODO verify if we should really name all the nodes, its better to name only the reused expression to avoid generating big numbers for aux.

    val usedTwiceAsValue = usedTwice.map(e => replaced.getOrElse(e, e)) //among the ast being reused, if one is among those to be substituted, then it is substituted.
    val UsedTwiceAskey = usedTwiceAsValue.filter(t => invertReplaced.contains(t)).map(e => invertReplaced(e))

    //  val needAffect: immutable.HashSet[AST[_]] = immutable.HashSet.empty ++ allNodes.filter { e => //we force affectation on those to facilitate latter processing @TODO forcer aussi l'affect sur les parametres données.
    //    e match { case Taail(_) | Heead(_) | Call1(_, _) | Call2(_, _, _) | Call3(_, _, _, _) => !usedTwiceAsValue.contains(e) case _ => false }    }
    val redops: Set[AST[_]] =immutable.HashSet.empty ++ allNodes.flatMap { _.redExpr } //set of expressions being reduced.
    val callAndHeadAndRedop = allNodes.filter((x: AST[_]) =>
      if(redops.contains(x)) true    else
        x match {
      case Taail(_) | Heead(_) | Call1(_, _) | Call2(_, _, _) | Call3(_, _, _, _) => true
      case a: ASTL[_, _] => a.shouldAffect
      case ast:AST[_]=> redops.contains(ast)
    })
    val inCall = callAndHeadAndRedop.flatMap(_ match { case c: Call[_] => c.args.filter(_.inputNeighbors.nonEmpty).toList case _ => List[AST[_]]() })
    val needAffect2 = callAndHeadAndRedop ::: inCall //.filter(  !usedTwiceAsValue.contains(_))
    //  for (e <- needAffect2   ) e.checkName()
    val affectExpList2 = immutable.HashSet.empty[AST[_]] ++ usedTwiceAsValue ++ needAffect2
    val affectExpList2ordered = allNodes.filter(affectExpList2.contains) //exploits the fact that allNodes are naturally topologically ordered to peserve the order for the list of affectations.
    for (e <- affectExpList2ordered) e.setNameIfNull()
    if ((immutable.HashSet.empty ++ affectExpList2ordered.map(_.name)).size < affectExpList2ordered.size) throw new RuntimeException("a name is reused two times") //since name are given by hand we check that no two names are equals
    for ((k, v) <- replaced) represent(v).setName(k.name) //the name of the key (to be replaced) is transfered to the replacing value.
    val toBeReplaced = affectExpList2 ++ UsedTwiceAskey
    val affectExpList = affectExpList2ordered.map(e => e.deDag(toBeReplaced - e, represent, replaced)).reverse //we remove e from usedTwice to avoid generate e=read(e) !!!!
    val t: TabSymb[InfoType[_]] = mutable.HashMap.empty
    t ++= affectExpList.map(e => (e.name, new InfoType(e.mym.name.asInstanceOf[T], Field())))
    t ++= f.p.toList.map(a => ("p" + a.name, InfoType(a, ParamD()))) //type of parameters this statement must happen after the addition of affects otherwise paramD varkind will be replaced by Affectk
   // affectExpList.map(e=>println(e.name + "="+ e.toStringTree))

    val affectInstr = affectExpList.map(e => Affect(e.name, e))
    val allUsedTwice = immutable.HashSet.empty[AST[_]] ++ usedTwiceAsValue ++ UsedTwiceAskey

    val newInstrsSys = allNodes.flatMap(e => {
      e.sysInstrs.map(i => new UsrInstr(i.c, i.exp.deDag(toBeReplaced, represent, replaced)) //  dedagify   exp used in system instructions
        .affectize(e, allUsedTwice.contains(i.exp), t))
    }).flatten //one flatten for list of list, and another one for None/Some
  //  print(string(t , "  | "))
    f.body = f.body.deDag(toBeReplaced, represent, replaced)
    new ProgData1(f, affectInstr ::: newInstrsSys.reverse, funs.map { case (k, v) ⇒ k -> v.deDagise() }, t, f.p.toList.map("p" + _.name), List()) //result parameter to be added letter by procedure step.
  }
}

/**
 * Stores all the data associated to a program, used for compilation
 *
 * @param tSymbVar ,  stores info about parameters or re-used expression,
 *                 @ Info: Type associated to variable, number of bits, to be completed progressively.
 * @param  instrs  instructions of the program (return, display, debug,...), the return instruction is stored separately.
 * @param  funs    list of functions used by the program, indexed by names.
 *                 * @ signature, list of parameters, Information of results.
 */





class ProgData1[+T](val f: Fundef[T], val instrs: List[Instr], val funs: iTabSymb[ProgData1[_]], val tSymbVar: TabSymb[InfoType[_]],
                    val paramD: List[String], val paramR: List[String]) {
  /**
   * @return the subfunction are printed like a list of pair (function_name, function.print), with macro sorted last
   */
  override def toString: String = paramD.mkString(" ") + "=>" + paramR.mkString(" ") + "\n" + instrs.reverse.mkString("") +
    DataProg.string(tSymbVar, "  | ") + "\n" + listOf(funs).mkString("\n \n  ")

  /** replaces function call by procedure call, introduces new names in tabSymb */
  def procedurise(): ProgData1[T] = {
    val procedureFun = funs.map { case (k, v) => k -> v.procedurise() }
    val hd: TabSymb[String] = mutable.HashMap.empty;
    val tl: TabSymb[String] = mutable.HashMap.empty
    val paramRmut = mutable.LinkedHashSet.empty[String] //we use LinkedHashSet as opposed to Hashset, to preserve the order of insertion because order of parameter is informational
    for (i <- instrs) i.buildhdtl(hd, tl)
    val paraResAffect = Instr.affectizeReturn(tSymbVar, paramRmut, f.body).flatMap(_.procedurIfy(hd, tl, tSymbVar))
    new ProgData1(f, instrs.flatMap(i => i.procedurIfy(hd, tl, tSymbVar)) ::: paraResAffect, procedureFun, tSymbVar, paramD, paramRmut.toList)
  }

  /**
   * Computes the number of bits of parameters, and affectation, and also internal nodes of all the ASTs.
   *
   *   @param nbitP: list of number of bits for each parameter assumed to be ASTLs.
   */
  def nbit(nbitP: List[Int]): ProgData2 = {
    val nbitExp: AstField[Int] = mutable.HashMap.empty
    val newFuns: TabSymb[ProgData2] = mutable.HashMap.empty
    val newtSymb: TabSymb[InfoNbit[_]] = mutable.HashMap.empty //we store the number of bits of parameters in newTabSymbVar:
    //Initalize the nbit of layers
    tSymbVar.map { case (nom, v) => if (v.k.isLayer) newtSymb += nom -> new InfoNbit(tSymbVar(nom).t, tSymbVar(nom).k, v.k.asInstanceOf[LayerField].nb) }

    newtSymb ++= (paramD zip nbitP).map { case (nom, nbi) => nom -> new InfoNbit(tSymbVar(nom).t, tSymbVar(nom).k, nbi) } //we assume that parameter are ASTLs
    val newInstrs = instrs.map(_.nbit(this, nbitExp, newtSymb, newFuns))
    new ProgData2(newInstrs, newFuns, newtSymb, paramD, paramR)
  }

}

    //  a.exp.isInstanceOf[Layer[_,_]] 