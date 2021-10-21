package compiler

import dataStruc.Align.{compose, invert}
import compiler.AST.{Call, Fundef, Layer2, Read, isCons, isNotRead}
import compiler.Circuit.{AstField, Machine, TabSymb, iTabSymb, iTabSymb2, listOf, newFunName}
import compiler.VarKind.{LayerField, MacroField, ParamD, ParamDR, ParamR, StoredField}
import dataStruc.{Align, Dag, DagInstr, toSet}
import dataStruc.DagInstr.setInputNeighbor
import Instr.{a, affectizeReturn}
import compiler.ASTB.Tminus1
import compiler.ASTBfun.{Fundef2R, redop}
import compiler.ASTL.ASTLg
import scala.collection.{Iterable, IterableOnce, Set, immutable, mutable}
import scala.collection.immutable.{HashMap, HashSet}

object DataProg {
  /** pring a map on several small lines, instead of one big line */
  def string[T](t: TabSymb[T], s: String): String = t.toList.grouped(4).map(_.mkString(s)).mkString("\n") + "\n"

  def lify(name: String): String = "ll" + name

  /**
   * @param f function to be compiled
   * @tparam T type of result returned by f.
   * @return A dataProg in highly compact forrm with four type of instructions which  are callProc to:
   *         -1 return (for the main)   2-show 3 -bug-4 memo (affectation to the next field for layers)
   *         Expression includes the following constructors:
   *         -1  AST Constructor: Delayed  Param | Call1 Call2 Call3 Coons Heead Taail | Read
   *         -2  ASTL Constructor: Binop  Coonst  Uno Redop  Clock Broadcast Send Transfer Sym
   *         The DFS algo of DAG visits all Delayed node recursively as soon as they are created
   *         Variables with varKind paramD and Layer are created
   ***/
  def apply[T](f: Fundef[T]): DataProg[InfoType[_]] = {
    def getLayers(l: List[AST[_]]) = l.collect { case la: Layer2[_] => la }

    def getSysInstr(l: List[AST[_]]): List[CallProc] = getLayers(l).flatMap(_.systInstrs2)

    //TODO build the layer structure here, exploit that we have it!
    val dag: Dag[AST[_]] = Dag()
    /** f.body  is the expression containing the value returned by the functions.
     * It  is the  access point to all the AST nodes needed to compute the function.
     * We use a fake call to a macro called "return" to represent the function's code */
    val main = CallProc("return", List(), List(f.body))
    var instrsCur = List(main) //instruction racine de tout
    var layers: List[Layer2[_]] = List()
    var callProcs: List[List[CallProc]] = List()
    //as we add generators, we possibly get new call to Display debug or memorize
    do try {
      val l: List[Layer2[_]] = getLayers(dag.addGenerators(instrsCur.flatMap(_.exps)))
      layers :::= l;
      val callProc: List[List[CallProc]] = (l.map(_.systInstrs2)).toList
      callProcs :::= callProc
      // instrsCur = l.flatMap(_.systInstrs2) }
      instrsCur = callProc.flatten
    }
    catch {
      case e@(_: dag.CycleException) =>
        dataStruc.Name.setName(f, "") //permet d'afficher les noms de variables du cycle et donc de
        //  Plus facilement identifier ou se trouve le cycle dans le programme
        for (a <- e.cycle)
          print(a + (if (a.name != null) (a.name + "-") else "-"))
        throw new dag.CycleException(Vector.empty)

    } while (!instrsCur.isEmpty)

    dataStruc.Name.setName(f, ""); //for ''grad'' to appear as a name, it should be a field of an object extending the fundef.
    val funs: iTabSymb[Fundef[_]] = immutable.HashMap.empty ++ dag.visitedL.collect { case l: Call[_] => (l.f.namef, l.f) }
    /** second  gathering of SysInstr which can access  the layer's name, because  setName has been called   */
    val instrs = main :: getSysInstr(dag.visitedL)
    val t2: TabSymb[InfoType[_]] = mutable.HashMap.empty
    // we will  store information about parameters, such as the number of bits. Therefore, we  store them in the symbol table.
    t2 ++= f.p.toList.map(a => ("p" + a.name, InfoType(a, ParamD())))
    // we will  store information about layers, such as the number of bits, displayfield, bugif fields.
    // Therefore, we  store them in the symbol table.
    //callProc memo is re-created therefore its  "precised" name is lost
    for ((l, cps) <- (layers zip callProcs))
      for (cp <- cps)
        cp.preciseName(l.name)
    t2 ++= layers.map(a => (lify(a.name), InfoType(a, LayerField(a.nbit))))

    new DataProg[InfoType[_]](new DagInstr(instrs, dag), funs.map {
      case (k, v) ⇒ k -> DataProg(v)
    }, t2, f.p.toList.map("p" + _.name), List())
  }
}

/**
 * Contains the compiled data, and all the functions used to implement the stage of compilation:
 * treify, procedurify, bitify, macroify, foldRegister, unfoldSpace
 *
 * @param funs  the macros
 * @param dagis the dag of instructions stored in reversed order.
 * @tparam U type of the info stored
 * @param tSymbVar symbol table
 * @param paramD   names of data parameters, provides  an order on them
 * @param paramR   names of result parameters , provides  an order on them
 */
class DataProg[U <: InfoType[_]](val dagis: DagInstr, val funs: iTabSymb[DataProg[U]], val tSymbVar: TabSymb[U],
                                 val paramD: List[String], val paramR: List[String], val coales: iTabSymb[String] = HashMap.empty) {


  override def toString: String = paramD.mkString(" ") + "=>" + paramR.mkString(" ") + "\n" +
    (if (coales.isEmpty) dagis else dagis.visitedL.map(_.asInstanceOf[Affect[_]].coalesc(coales))) +
    tSymbVar.toList.grouped(4).map(_.mkString("-")).mkString("\n") + "\n" + listOf(funs).mkString("\n \n  ")

  /** add new symbol created through affectize */
  private def updateTsymb[U](l: List[AST[_]], v: VarKind) = {
    tSymbVar.asInstanceOf[TabSymb[InfoType[_]]] ++= l.map((e: AST[_]) => (e.name, new InfoType(e.mym.name, v)))
  }

  /**
   * @return the DAG of AST becomes a forest of tree, and we we build a Dag of Instructions instead which include.
   *         1- as before callProc to  -1 return    2-show 3 -bug- 4 memo (affectation )
   *         2- pure affectation of AST used two times or more.
   *         variable for those affectation are created with VarKind "Field"
   *         Delayed Constructors are removed from Expressions
   *         Param are replaced by Read with the letter 'p' added to the name
   *         Layers are replaced by Read with the letter 'll' added to the name
   *
   */
  def treeIfy(): DataProg[InfoType[_]] = {
    val p = this.asInstanceOf[DataProg[InfoType[_]]]
    val dagis2 = dagis.affectIfy(p.dagis.inputTwice) //also replaces access to data parameters+layers by read
    //expression of the Affectation generated are stored in dagis.newAffect, they correspond precisely to nonGenerators.
    val (layerFields, macroFields) = dagis.newAffect.map(_.exp).partition(isLayerFieldE(_))
    p.updateTsymb(macroFields, MacroField()) // when a variable is used twice it should be evaluated in a macro
    //which means its type should be set to MacroField
    p.updateTsymb(layerFields, StoredField()) //This is excepted for affectation of the form dist<-lldist,
    // the type of dist is set to storedLayer
    // paramD varkind  could  be replaced by Affect , but this should not happen because of the added letter 'p' for the parameter.
    // if a parameter is used two times, the generated affectation will generate a read without the 'p'
    new DataProg(dagis2, funs.map { case (k, v) ⇒ k -> v.treeIfy() }, p.tSymbVar, paramD, paramR)
  }

  def treeIfy2(): DataProg[InfoType[_]] = {
    val p = this.asInstanceOf[DataProg[InfoType[_]]]
    val iT = p.dagis.inputTwice.filter(isNotRead)
    val u = 0
    /* val dagis2 = dagis.affectIfy(iT) //also replaces access to data parameters+layers by read

    //xpression of the Affectation generated are stored in dagis.newAffect, they correspond precisely to nonGenerators.
     val (layerFields, macroFields) = dagis.newAffect.map(_.exp).partition(isLayerFieldE(_))
     p.updateTsymb(macroFields, MacroField()) // when a variable is used twice it should be evaluated in a macro
     //which means its type should be set to MacroField
     p.updateTsymb(layerFields, StoredField()) //This is excepted for affectation of the form dist<-lldist,
     // the type of dist is set to storedLayer
     // paramD varkind  could  be replaced by Affect , but this should not happen because of the added letter 'p' for the parameter.
     // if a parameter is used two times, the generated affectation will generate a read without the 'p'*/
    new DataProg(dagis, funs.map { case (k, v) ⇒ k -> v.treeIfy2() }, p.tSymbVar, paramD, paramR)
  }

  /**
   * @return replaces function call by procedure call
   *         "return " callProc together with Cons expression are replaced by  affectations  to result parameters,
   *         Call AST nodes are replaced by   callProc instructions
   *         x<-Heead y<-Taail are replaced by directly passing x to the call Proc , written as an affectation of x,y
   *         instructions  of the form: id<-tail  id<-head, return   becomes useless. They are filtered out
   *         variable for effective (resp. formal) result are created with VarKind "StoredField" (resp. ParamR)
   */
  def procedurIfy(): DataProg[InfoType[_]] = {
    val p = this.asInstanceOf[DataProg[InfoType[_]]]
    val dagis2 = dagis.affectIfy(isCons)
    p.updateTsymb(dagis.newAffect.map(_.exp), MacroField())
    val hd: TabSymb[String] = mutable.HashMap.empty;
    val tl: TabSymb[String] = mutable.HashMap.empty
    for (i <- dagis2.visitedL) i.buildhdtl(hd, tl)
    /** "return CallProc instruction" containing the body of the function */
    val main = dagis2.allGenerators.find(_.isReturn).get.asInstanceOf[CallProc]
    /** names of variable storing the result parameters ,
     * LinkedHashSet as opposed to Hashset,   preserves the order of insertion
     * and thus, the order of parameter, which is informational */
    val paramRmut = mutable.LinkedHashSet.empty[String]
    /** transformation if formulated as an instruction rewriting
     * replace the "return" callProc by  affectations  to result parameters, and then
     * replace Call AST nodes by   callProc instructions
     * filters out instructions which becomes useless, of the form: id<-tail  id<-head, return */
    val rewrite2: Instr => List[Instr] = (i: Instr) => {
      if (i.isReturn) affectizeReturn(p.tSymbVar, paramRmut, i.exps.head).flatMap(_.procedurIfy(hd, tl, p.tSymbVar))
      else i.procedurIfy(hd, tl, p.tSymbVar)
    }
    new DataProg(dagis2.propagate(rewrite2), funs.map { case (k, v) => k -> v.procedurIfy() }, p.tSymbVar, paramD, paramRmut.toList)
  }

  /**
   * Computes the number of bits of all variables: parameters (effective and formal)
   * ,  affectation, and also internal nodes of all the ASTs.
   *
   * @param nbitP : list of  each parameter's bit size, assumed to be ASTLs.
   * @return Program data including number of bits  available in the symbol table
   *         a macro signature now includes bit size of parameters.
   *         So if a macro is called two times with different bitsize, two macros are compiled
   *         The affectation for redops should be generated in foldRegister
   *         We generate them now so that we can also compute the number of bits for the corresponding variables.
   *         //¯TODO show of storedLayer must be handled after macroification
   **/
  def bitIfy(nbitP: List[Int]): DataProg[InfoNbit[_]] = {
    val p = this.asInstanceOf[DataProg[InfoType[_]]]

    /** set of expressions being reduced. */

    /** We generate also variable which are effective data parameters for called macro
     * their kind is set to StoredField() */
    val effectiveDataParam: HashSet[AST[_]] = HashSet() ++ dagis.allGenerators.flatMap(
      { case cp@CallProc(p, names, exps) => if (Instr.isProcessedInMacro(p)) List() else exps.filter(isNotRead(_)); case _ => List() })
    val dagis1 = dagis.affectIfy(effectiveDataParam(_))
    /** effective result parameters which were already variables need to be re-registered as storedFields */
    val newStoredFiedl: List[AST[_]] = effectiveDataParam.toList.filter((a: AST[_]) => AST.isNotRead(a) || p.tSymbVar(a.name).k == MacroField())
    p.updateTsymb(newStoredFiedl, StoredField())

    val l = dagis1.dagAst.visitedL.asInstanceOf[List[ASTLt[_, _]]]
    val redops: HashSet[AST[_]] = HashSet() ++
      l.flatMap {
        _.redExpr
      } ++ l.filter(_.isRedop)
    val affected = dagis1.visitedL.filter(_.isInstanceOf[Affect[_]]).map(_.exps.head)

    val redops2 = redops -- affected //we do not need to affectify, it is already affectified

    /** values being reduced must be id of variable
     * so we affectify those, before bitIfying,
     * because that puts new ids in the symbol table
     * for  which we will also need to know the size
     * We also affectify the reduced value in order to reuse the register
     * which accumulates the reduction */
    val dagis2 = dagis1.affectIfy(redops2(_));
    p.updateTsymb(dagis1.newAffect.map(_.exp), MacroField())


    val nbitExp: AstField[Int] = mutable.HashMap.empty
    val newFuns: TabSymb[DataProg[InfoNbit[_]]] = mutable.HashMap.empty
    /** stores the number of bits of parameters which are assumed to be ASTLs */
    val newtSymb: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    //adds param's bit
    newtSymb ++= (paramD zip nbitP).map {
      case (nom, nbi) => nom -> new InfoNbit(tSymbVar(nom).t, tSymbVar(nom).k, nbi)
    }
    //adds layers's bit
    val layersName: List[String] = tSymbVar.keys.filter(AST.isLayer(_)).toList

    for (nom <- layersName) {
      val d = tSymbVar(nom)
      newtSymb.addOne(nom, new InfoNbit(d.t, d.k, d.k.asInstanceOf[LayerField].nb))
    }
    val rewrite: Instr => Instr = _.bitIfy(p, nbitExp, newtSymb, newFuns)
    // we bitify all the instructions in reverse order
    // because instructions are stored in reversed order
    // and computing the number of bits needs to follow the natural order
    new DataProg(dagis2.propagateReverse(rewrite), newFuns, newtSymb, paramD, paramR)
  }

  /**
   *
   * @return true if function is a leaf function,
   *         not calling other function, so no stored field
   *         and therefore directly executable as a loopMacro on CA   */
  private def isLeafCaLoop: Boolean = funs.isEmpty && !tSymbVar.valuesIterator.exists(_.k.isStoredField)

  /**
   *
   * @param e expression we want to check
   * @return true if e reads a layer
   */
  private def isLayerFieldE(e: AST[_]): Boolean = e match {
    case AST.Read(s) => tSymbVar(s).k.isLayerField
    case _ => false
  }

  def macroIfy(): DataProg[InfoNbit[_]] = {
    def needStored(s: String): Boolean = tSymbVar(s).k.needStored

    /**
     * @param i
     * @return true if needs to store the results
     */
    def resultNeedStored(i: Instr) = i.names.filter(needStored).nonEmpty || i.tobeProcessedInMacro

    /**
     * Creates a subFunction from a set of Affectation supposed to be in topological order (not completely sure, though)
     * DR parameter are repeated, but will be removed from results, when compiling the call, and the header.
     *
     * @param finstrs a set of affectation forming a connected component.
     */
    def builtFun(finstrs: Iterable[Instr]): DataProg[InfoNbit[_]] = {
      val pureAffect = finstrs.map(_.callProcToAffect) //transforms memo calls into affect
      val fparamR = pureAffect.filter(resultNeedStored).toList
      val fparamRname = fparamR.flatMap(_.names).filter(needStored).toList
      // val fparamD = toSet(finstrs.map(_.asInstanceOf[Affect[_]].exp.symbols.filter(needStored)).toList.flatten).toList
      val fparamD = toSet(pureAffect.flatMap(_.exps).flatMap(_.symbolsExcepLayers).filter(needStored))
      /** Variables that are computed within new function should not be passed as data but as DR      */
      val fparamDwithoutR = fparamD.filter(!fparamRname.contains(_)).toList
      //if there is paramD which are also parameR then fparamDwithoutR va etre strictement plus petit que fparamD
      if (fparamDwithoutR.size < fparamD.size)
        throw new RuntimeException("Macro has parameter which are both data and result")
      val newtSymbVar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
      val t = tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]]
      for (p <- fparamDwithoutR) {
        val old = t(p); newtSymbVar += p -> new InfoNbit(old.t, ParamD(), old.nb)
      }
      for (p <- pureAffect) for (n <- p.names) {
        val old = t(n)
        newtSymbVar += n -> new InfoNbit(old.t, if (!needStored(n)) MacroField() else if (fparamDwithoutR.contains(n)) ParamDR() else ParamR(), old.nb)
      }

      setInputNeighbor(pureAffect.toList.asInstanceOf[List[Instr]]) // when using a data parameter in paramD,
      // we should not include the instructions which were computing those parameter
      val newDagis = new DagInstr(fparamR) //instructions computing results are the roots.
      new DataProg(newDagis, mutable.HashMap.empty, newtSymbVar, fparamDwithoutR, fparamRname)
    }

    /**
     * @param finstrs instructions forming a connected component
     * @return true if the instructions use only  concat or elt,
     *         it is not necessary to create a function, in this case.
     */
    def NeedBuiltFun(finstrs: Iterable[Instr]): Boolean = {
      for (i <- finstrs.filter(_.isInstanceOf[Affect[_]])) if (!i.asInstanceOf[Affect[_]].exp.asInstanceOf[ASTL.ASTLg].justConcats) return true;
      false
    }

    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    if (isLeafCaLoop) return p


    /**
     * second instruction is an input neighbor of first
     * ie it computes a variable that is read by second instructions
     * this link is preserved but if this variable need not be stored
     * if it needs to be stored  the source will remain in the main loop
     * we check if the expression of the source is a layer such as lldist
     * in which case we break the connection because the instruction
     * dist <- lldist  to remain in the main loop
     **/
    val proximity2: (Instr, Instr) => Boolean = {
      case (Affect(_, _), Affect(name, exp)) => {
        !needStored(name) //&& !isLayerFieldE(exp)
      };
      case (CallProc(namep, _, _), Affect(name, exp)) =>
        val r = Instr.isProcessedInMacro(namep) && !needStored(name) //&& !isLayerFieldE(exp) //works for bug and memo
        r
      case _ => false
    }
    val newFuns: TabSymb[DataProg[InfoNbit[_]]] = mutable.HashMap.empty

    /**
     * @param g instructions forming a connected component
     * @return a CallProc to a  function that is created as a side effect, from those instructions.
     */
    def transform(g: Iterable[Instr]): List[Instr] = {
      if (g.size == 1 || !NeedBuiltFun(g)) return g.toList
      val name = newFunName()
      newFuns.addOne(name -> builtFun(g))
      List(Instr(name, newFuns(name))) //computes a CallProc to the new function
    }

    val newDagis: Dag[Instr] = dagis.quotient2(proximity2, transform)
    val newTsymbVar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    //we filter out macro Fields
    for ((name, info) <- p.tSymbVar)
      if (info.k != MacroField())
        newTsymbVar.addOne(name -> info)
    new DataProg(newDagis, newFuns ++ funs.map { case (k, v) ⇒ k -> v.macroIfy() }, newTsymbVar, paramD, paramR)
  }

  def addParamRtoDagis(dagis1: DagInstr) = {
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    val rewrite1: Instr => List[Instr] = (i: Instr) => a(i).addParamR(p.tSymbVar)
    dagis1.propagate(rewrite1)
  }


  /**
   *
   * @return dag of zones plus  dagInstr modified by adding shift instructions when necessary
   */
  def zones(dagis1: DagInstr): (DagInstr, Dag[Zone]) = {
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    //nothing to do fro non macro
    /** used to collect econstraint  generated when aligning */
    val constraints: TabSymb[Constraint] = mutable.HashMap.empty

    val rewrite2: Instr => List[Instr] = (i: Instr) =>
      if (i.isTransfer) a(i).align(constraints, p.tSymbVar) else
        List(i)
    val dagis2: DagInstr = dagis1.propagate(rewrite2)
    print("ererererererererererererererererererererererererererererererererererererererererererererer\n" + dagis2)
    if (!constraints.isEmpty) println("Constraint: " + constraints) //we check constraints generated
    //for (i <- dagis2.visitedL) i.reset //clean stuff being generated when creating macro
    for (i <- dagis2.visitedL) i.reset //clean stuff being generated when creating macro
    //adds the names of shifted variables
    if (isLeafCaLoop) //shifted variables are introduced in macro (If cycles are present)
      for (i <- dagis2.visitedL)
        if (i.isShift) {
          val n = a(i).name
          val d: InfoNbit[_] = p.tSymbVar(n.drop(5)) //info about not shifted variable
          p.tSymbVar.addOne(n, new InfoNbit(d.t, d.k, d.nb))
        }

    // val notFolded  = mutable.HashSet.empty[String] //we must remember variables that could not be folded.
    /**
     * used to build zone defined as connected components of identical locus: transfer or simplicial
     * we start by target which is the fist component and tries to add source which is the second comonent
     * * second component is source, therefore the first can be callProc*/
    val proximity2: (Instr, Instr) => Boolean =
      (x: Instr, y: Instr) => x.isTransfer == y.isTransfer &&
        !y.shiftandshifted(x) //toto is an inputneighbors of shiftoto, but it is a fake binding used to
    //ensure that shiftoto is scheduled after toto's affectation,
    // this fake binding is identified  using the predicate shiftandshifted and then neutralized
    // because it must no be used to compute alignement to root.

    def transform(g: Iterable[Instr]): List[Zone] = List(Zone(constraints, g.asInstanceOf[Iterable[Affect[_]]]))

    /**
     * We here assume that the zones form a Dag, it could fail, in which case we should look back to the code
     * and see if we can formulate the code differently so as to obtain a Dag
     * a Dag for zones simplifies a lot the comming picking phase
     */
    val zoneDag: Dag[Zone] = dagis2.quotient2(proximity2, transform)
    zoneDag.visitedL.map(_.addPartitionOut()) //set partition constraints towards output neighbors
    //now we know if the TCC will fold, before we pick, we could try to further constrain the cycle so as to reuse
    //delayed variables in order to avoid introducing new registers
    zoneDag.visitedL.map(_.setFoldConstrSimplicial())
    (dagis2,
      zoneDag)
  }


  /**
   *
   * @param m
   * @param d
   * @return a first simple version of muInstructions that does not fold reduction and do not consider  shift
   */

  private def muInstr(m: Machine, d: DagInstr): Map[String, List[Instr]] = { //: (Map[String, List[Instr]],TabSymb[InfoNbit[_]] )
    require(isLeafCaLoop)
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    var muIs: iTabSymb2[List[Instr]] = HashMap.empty
    //val tZone: Map[String, Zone] = DagInstr.defby(zones.visitedL)
    for (i <- d.visitedL) muIs += a(i).name -> i.unfoldSpace(m, p.tSymbVar)
    muIs
  }

  /**
   *
   * @param d
   * @return computes the mu Instructions of the main, which remains in the same order, no scheduling needed.
   */
  private def muInstrMain(d: DagInstr) = { //: (Map[String, List[Instr]],TabSymb[InfoNbit[_]] )
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    var tSymbScalar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    for ((name, info: InfoNbit[_]) <- p.tSymbVar) {
      val names = info.locus.deploy(name)
      for (n <- names)
        tSymbScalar.addOne(n -> tSymbVar(name).asInstanceOf[InfoNbit[_]].scalarify)
    }
    (d.visitedL.flatMap(_.unfoldSpace(null, p.tSymbVar)), tSymbScalar)
  }


  private def deploy(s: String) = tSymbVar(s).locus.deploy(s)

  /**
   *
   * @param paramR
   * @return finds out if an "R" has been added due to the fact that it was a result used to compute a redop
   *         if so, modifies the result's name
   */
  private def addsAnR(paramR: String) = if (tSymbVar.contains(paramR + "R")) paramR + "R" else paramR


  def unfoldSpace(m: Machine): DataProg[InfoNbit[_]] = {
    val funs2 = funs.map { case (k, v) => k -> v.unfoldSpace(m) }
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    if (!isLeafCaLoop) {
      val (muI, tSymbScalar) = muInstrMain(dagis) //computes muI of callProc and direct affectation
      return new DataProg(DagInstr(muI), funs2, tSymbScalar, paramD.flatMap(deploy(_)), paramR.flatMap(deploy(_)))
    }
    val dagis1bis = addParamRtoDagis(dagis) //add a new paramR after redop which is done in a  macroField todo avoid recomputing the whole dag
    val (dagis2: DagInstr, z) = zones(dagis1bis) //the computation of zones introduces shifted variables
    // therefore it must be done before muInstructions
    val muI = muInstr(m, dagis2) //TODO inspect muI's tm1 to refine constraints so as to fold vortex
    z.visitedL.reverse.map(_.pick()) //pick is done starting from the first instruction
    val tZone: Map[String, Zone] = DagInstr.defby(z.visitedL)
    val defI: Map[String, Instr] = dagis2.defby
    val (muI2, tSymbScalar, coalesc) = permuteAndFixScheduledMu(muI, dagis2, tZone, defI) // revisit muI 's'reduce when reduced exression is folded
    //we separate the reduction in two parts: one that can do at tm1 and the rest that is done now.
    val muI3: List[Affect[_]] = scheduleMuCode(muI2, dagis2, defI, tZone).toList.asInstanceOf[List[Affect[_]]]
    val iT = DagInstr(muI3).inputTwice.filter(isNotRead) //we exploit the DAG form to find out about usedTwice exp
    //if the factorized expression is just a << or >> we better just recompute it
    //print("____|____|____|____|____|____|____|____|____|____|____|____|\n"+muI3)
    //val muI4 = muI3.map(_.coalesc(coalesc))
    new DataProg(DagInstr(muI3), funs2, tSymbScalar, paramD.flatMap(deploy(_)), paramR.map(addsAnR(_)).flatMap(deploy(_)), coalesc)
  }

  /**
   *
   * @param muI   muInstruction in canonical order grouped per instruction's defined name
   * @param dagis instructions needed to compute
   * @param tZ    zones names
   * @return hashmap of muInst assoicated to inst, now scheduled between the 6
   */
  def permuteAndFixScheduledMu(muI: Map[String, List[Instr]], dagis: DagInstr,
                               tZ: Map[String, Zone], defI: Map[String, Instr]) = {
    var oldmuI = muI //it will be modified to remove the tm when doing reduction
    var newMuI: HashMap[String, List[Instr]] = HashMap.empty
    /** stores the name and type of variables produced by spatial unfolding, after register folding */
    var tSymbScalar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    /** stores a mapping to coalesced registers    */
    var coalesc: iTabSymb[String] = HashMap.empty

    /**
     *
     * @param name variable affected by an instruction
     * @return muInst assoicated to inst, now scheduled
     *
     */
    def permuteAndFixScheduledMu2(name: String): List[Instr] = {
      val i = defI(name) //instruction
      if (newMuI.contains(name)) return newMuI(name) //muInstruction's new schedule has already been computed
      val permuted: List[Instr] =
        if (a(i).isRedop) foldRedop(a(i))
        else if (i.isV) oldmuI(name) //simplest case
        else if (i.isFolded(tZ)) {
          if (i.isShift) foldShift(a(i))
          else {
            val s = i.mySchedule(tZ)
            if (s != null) dataStruc.Align.compose2(s, oldmuI(name).toSeq).toList
            else throw (new Exception("problem in aligning on root"))
          }
        }
        else if (!i.isTransfer) oldmuI(name) //canonical order, no need to permute
        else throw (new Exception("look why transfer zone is not folded in order to guess what to do"))
      newMuI += name -> permuted;
      // computes coalesc mapping and tSymbScalar
      if (!a(i).isRedop) { //for redop the coalesc mapping and tSymbScalar are already done
        val l = a(i).locus.get
        val names = l.deploy(i.names.head)
        if (i.isFolded(tZ) && tSymbVar(i.names.head).k != ParamR()) {
          for (n <- names)
            coalesc += (n -> i.names.head) //we coalesc several symbol
          //and we add the single coalesced symbol
          tSymbScalar.addOne(i.names.head -> tSymbVar(i.names.head).asInstanceOf[InfoNbit[_]].scalarify)
        }
        else for (n <- names) //no coalesced needed, we add several symbols
          tSymbScalar.addOne(n -> tSymbVar(i.names.head).asInstanceOf[InfoNbit[_]].scalarify)
      }
      permuted
    }

    /**
     *
     * @param i instruction doing the affect
     * @return scheduled  muinstruction for redop.
     *         it depends wether the reduced field is folded or not
     */
    def foldRedop(i: Affect[_]) = {
      /**
       *
       * @param name   instruction's name
       * @param muName muInstruction that should be removed tm1
       */
      def detm1ise(name: String, muName: String) = {
        oldmuI = oldmuI + (name -> oldmuI(name).map(
          _.detm1ise(muName)))
      }

      val op = a(i).exp.asInstanceOf[ASTL[_, _]].opRedop
      val inputInst = i.inputNeighbors.head
      if (!inputInst.isFolded(tZ)) oldmuI(i.name) // if reduced field is not folded we leave as it was:a single expression
      else {
        val l = a(i).locus.get.asInstanceOf[S]
        val r1 = a(i).ring.get
        val r = repr(r1).asInstanceOf[repr[Ring]]
        val d = l.density
        val cpt = Array.fill[Int](d)(0) //used to suffix name
        val cptTm1 = Array.fill[Int](d)(0) //used to suffix name of delayed sum
        val tm1Sum: Array[Int] = Array.fill[Int](d)(0) //number of delayed for each component
        val result = new Array[Instr](6)
        val names = l.deploy(i.name)
        val iInputMuInsts: Array[Instr] = oldmuI(inputInst.names.head).toArray //inputNeighbor which is reduced
        val inputShedule: Array[Int] = inputInst.mySchedule(tZ) //schedule of inputNeighbor
        val iInputMuInstOrdered = Align.compose3(inputShedule, iInputMuInsts)
        for (j <- 0 to 5)
          tm1Sum(l.proj(inputShedule(j))) +=
            (if (iInputMuInstOrdered(j).exps(0).isInstanceOf[Tminus1[_]]) 1 else 0)
        val isTm1 = iInputMuInstOrdered.map(_.exps.head.isInstanceOf[Tminus1[_]])
        val scheduleOfLastAffectedTm1 = isTm1.lastIndexOf(true)
        val nbDelayed = isTm1.filter(_ == true).size
        // val optionalPrefix = if (tSymbVar(i.name).k == ParamR()) "#Reg" else ""
        for (j <- 0 to 5) { //for folding of input  to work, the reduction must accumulate
          val iInputMuInst: Affect[_] = a(iInputMuInstOrdered(j)) //muInst read
          val numI = l.proj(inputShedule(j)) //numI select the target component of the simplicial vector produced by redop
          if (tm1Sum(numI) < 2) //it is not worth doing a delayed sum
          {
            val nameOfAffectedPrevious = names(numI) + "#" + cpt(numI)
            cpt(numI) += 1;

            val nameOfAffectedNow = names(numI) +
              (if (cpt(numI) * d >= 6) "" else "#" + cpt(numI)) //last affected component does no get an integer prefix
            val coalescedName = (if (i.isFolded(tZ) || i.isV) i.name else names(numI)) //+ (if (cpt(numI) * d >= 6) "" else optionalPrefix)
            coalesc += (nameOfAffectedNow -> coalescedName)
            tSymbScalar.addOne(coalescedName -> tSymbVar(i.name).asInstanceOf[InfoNbit[_]]) //.regifyIf(coalescedName != names(numI)))
            val iInputMuInstName = iInputMuInst.names.head
            val readNextMuVar = Instr.readR(iInputMuInstName, r)
            val readCurrentRedVar = Instr.readR(nameOfAffectedPrevious, r)
            val newMuInstrExp =
              if (cpt(numI) == 1) readNextMuVar //the first myInstruction is a simple affectation
              else Instr.reduceR(readCurrentRedVar, readNextMuVar, //the other apply the binary operator of the muInstruction
                op.asInstanceOf[redop[Ring]], r)
            result(j) = Affect(nameOfAffectedNow, newMuInstrExp)
          }
          else //we do a delayed sum with at least two term in it
          {
            val cptt = if (isTm1(j)) cptTm1(numI) else cpt(numI)
            val iInputMuInstName = iInputMuInst.names.head
            detm1ise(inputInst.names.head, iInputMuInstName) //correct oldMui, remove the tm1
            newMuI = newMuI - inputInst.names.head
            permuteAndFixScheduledMu2(inputInst.names.head) //recompute newMui from oldMui
            val tm1Opt = if (isTm1(j)) "tm1"
            else"" //suffixe optionnel a rajouter
            val nameOfAffectedPrevious = names(numI) + tm1Opt + "#" + cptt
            if (isTm1(j)) cptTm1(numI) += 1 else cpt(numI) += 1;
            val onlyTm1 = tm1Sum(numI) * d == 6
            val onlyTm1Last = onlyTm1 && cptTm1(numI) == tm1Sum(numI) //true for final reduction when only tm1
            val firstNonTm1 = (cpt(numI) == 1) && !(isTm1(j))
            val lastNonTm1 = ((cpt(numI) + tm1Sum(numI)) * d == 6) && (!isTm1(j)) // representing the reduction for each component
            val lastTm1 = (cptTm1(numI) == tm1Sum(numI)) && (isTm1(j)) // representing the reduction for each component
            if (firstNonTm1)
              print("toto")
            val nameOfAffectedNow = names(numI) + (if (onlyTm1 && lastTm1) "" else //when there is only tm1 then the last term has no prefix
              (tm1Opt +
                (if (lastNonTm1) "" else ("#" + (cptt + 1))) //last affected component does no get an integer prefix
                ))

            val coalescedName = if (i.isFolded(tZ) || i.isV) i.name else names(numI)
            val coalescedNameTm1 = coalescedName + (if (!onlyTm1Last) tm1Opt else "")
            coalesc += (nameOfAffectedNow -> coalescedNameTm1)
            tSymbScalar.addOne(coalescedNameTm1 -> tSymbVar(i.name).asInstanceOf[InfoNbit[_]]) //.regifyIf(coalescedName != names(numI)))


            val readNextMuVar = Instr.readR(iInputMuInstName, r)
            val nameOfFinalAffectedTm1 = names(numI) + "tm1" + "#" + tm1Sum(numI)
            //iInputMuInstOrdered(scheduleOfLastAffectedTm1).names.head+"tm1#" + nbDelayed
            val readCurrentRedVar =
              if (firstNonTm1) //we retrieve the other sum using a tm1, it introduces another Z variable, to be removed later
                Instr.tm1R(Instr.readR(nameOfFinalAffectedTm1, r), r)
              else
                Instr.readR(nameOfAffectedPrevious, r)
            val newMuInstrExp =
              if (cptTm1(numI) == 1 && isTm1(j)) readNextMuVar //the first myInstruction is a simple affectation
              else Instr.reduceR(readCurrentRedVar, readNextMuVar, //the other apply the binary operator of the muInstruction
                op.asInstanceOf[redop[Ring]], r)
            val newMuInstrExpTm1 = if (onlyTm1Last) Instr.tm1R(newMuInstrExp, r) else newMuInstrExp
            result(j) = Affect(nameOfAffectedNow, newMuInstrExpTm1)
          }
        }
        result.toList
      }
    }

    def foldRedop2(i: Affect[_]) = {
      val op = a(i).exp.asInstanceOf[ASTL[_, _]].opRedop
      val inputInst = i.inputNeighbors.head
      if (!inputInst.isFolded(tZ)) oldmuI(i.name) // if reduced field is not folded we leave as it was:a single expression
      else { // representing the reduction for each component
        val l = a(i).locus.get.asInstanceOf[S]
        val r1 = a(i).ring.get
        val r = repr(r1).asInstanceOf[repr[Ring]]
        val d = l.density
        val cpt = Array.fill[Int](d)(0) //used to suffix name
        val cptTm1 = Array.fill[Int](d)(0) //used to suffix name of delayed sum
        val result = new Array[Instr](6)
        val names = l.deploy(i.name)
        val iInputMuInsts = oldmuI(inputInst.names.head) //inputNeighbor which is reduced
        val inputShedule: Array[Int] = inputInst.mySchedule(tZ) //schedule of inputNeighbor
        // val optionalPrefix = if (tSymbVar(i.name).k == ParamR()) "#Reg" else ""
        for (j <- 0 to 5) { //for folding of input  to work, the reduction must accumulate
          val numI = l.proj(inputShedule(j)) //numwI select the target component of the simplicial vector produced by redop
          val iInputMuInst = a(iInputMuInsts(inputShedule(j))) //muInst read
          val isTm1 = iInputMuInst.exp.isInstanceOf[Tminus1[_]]
          val nameOfAffectedPrevious = names(numI) + "#" + cpt(numI)
          cpt(numI) += 1;
          val nameOfAffectedNow = names(numI) +
            (if (cpt(numI) * d >= 6) "" else "#" + cpt(numI)) //last affected component does no get an integer prefix
          val coalescedName = (if (i.isFolded(tZ) || i.isV) i.name else names(numI)) //+ (if (cpt(numI) * d >= 6) "" else optionalPrefix)
          coalesc += (nameOfAffectedNow -> coalescedName)
          tSymbScalar.addOne(coalescedName -> tSymbVar(i.name).asInstanceOf[InfoNbit[_]]) //.regifyIf(coalescedName != names(numI)))
          val iInputMuInstName = iInputMuInst.names.head
          val readNextMuVar = Instr.readR(iInputMuInstName, r)
          val readCurrentRedVar = Instr.readR(nameOfAffectedPrevious, r)
          val newMuInstrExp =
            if (cpt(numI) == 1) readNextMuVar //the first myInstruction is a simple affectation
            else Instr.reduceR(readCurrentRedVar, readNextMuVar, //the other apply the binary operator of the muInstruction
              op.asInstanceOf[redop[Ring]], r)
          result(j) = Affect(nameOfAffectedNow, newMuInstrExp)
        }


        result.toList
      }
    }

    /**
     *
     * @param i shifting instruction
     * @return muInstr generated from a shift are computed using specific processing
     */
    def foldShift(i: Affect[_]) = {
      assert(i.isShift) //we must have a shift
      val muInstUnShift = permuteAndFixScheduledMu2(i.unShifted) //we compute the shift schedule from the argument's scheduile
      val (_, List(last)) = muInstUnShift.splitAt(5) //isolate last instruction/we put last instruction first
      val Ishifted: Instr = defI(i.unShifted) //apply same permutation as muInstUnShift
      val s2 = Ishifted.mySchedule(tZ)
      val permutedMuShifted = dataStruc.Align.compose2(s2, oldmuI(i.name).toSeq)
      //replace first MUaffectation of permutedMushifted by last MuAffectation
      val inew = Affect(permutedMuShifted(5).names(0), last.exps(0))
      permutedMuShifted(5) = inew
      ASTL.rotR(permutedMuShifted, 1).toList
    }

    for (name <- oldmuI.keys) permuteAndFixScheduledMu2(name)
    (newMuI, tSymbScalar, coalesc)
  }

  /**
   * produce a list of muInstr in the right order.
   *
   * @param muI
   * @param dagis
   */
  def scheduleMuCode(muI: Map[String, List[Instr]], dagis: DagInstr, defI: Map[String, Instr], tZone: Map[String, Zone]) = {
    /** which instruction is using this variable */
    var muI2: Map[String, List[Instr]] = muI //HashMap.empty
    val tabInstr = dagis.visitedL.toArray
    var isUsing: HashMap[String, HashSet[String]] = HashMap.empty
    var usedVar2: HashMap[String, HashSet[String]] = HashMap.empty
    var token: HashMap[(String, String), Int] = HashMap.empty
    var priority: HashMap[String, Int] = HashMap.empty
    var inputInstr: HashSet[String] = HashSet.empty
    var inputLessInstr: HashSet[String] = HashSet.empty

    def diff(t2: String) = -priority(t2)
    val readyInstr = new collection.mutable.PriorityQueue[String]()(Ordering.by(diff))
    var prio = 0
    var result: List[Instr] = List()
    for (i <- dagis.visitedL) {
      var u = i.usedVars
      //for shifttoto instruction we must add used(toto) to used (shiftToto)
      if (i.isShift)
        u ++= defI(i.names.head.drop(5)).usedVars
      if (u.isEmpty) inputLessInstr += i.names.head
      usedVar2 += i.names.head -> u
      for (v <- u) {
        isUsing += v -> (if (isUsing.contains(v)) (isUsing(v) + i.names.head)
        else HashSet(i.names.head))
        token += (i.names.head, v) -> 0
      }
      priority += i.names.head -> prio
      prio += 1
    }

    /**
     *
     * @param i
     * @return true if contains token on output links
     */
    def noTokenOutput(i: String): Boolean = {
      if (isUsing.contains(i))
        for (i2 <- isUsing(i))
          if (token(i2, i) > 0) return false
      true
    }

    /**
     *
     * @param i   variable name set by an instruction,
     * @param   l locus of instruction
     * @return true if contains token on output links
     */
    def addSeveralToken(i: String, l: Locus): Unit =
      if (isUsing.contains(i))
        for (i2 <- isUsing(i)) {
          val densityOut = tSymbVar(i2).locus.density
          val nbToken =
            if (defI(i).isFolded(tZone))
              Math.max(1, densityOut / l.density) //  >1if output neigbor has higer density
            else //i triggers only once, and sends all its token which are equal to its density
              densityOut
          token += ((i2, i) -> (token(i2, i) + nbToken))
        }

    /**
     *
     * @param i name of an i
     * @return true if each input line of instruction i contains at least one token
     */
    def oneTokenEveryInput(i: String): Boolean = {
      if (usedVar2.contains(i))
        for (i2 <- usedVar2(i))
          if (token(i, i2) < 1)
            return false
      return true
    }

    /**
     *
     * @param i register set by an instruction
     */
    def consumeToken(i: String) =
      if (usedVar2.contains(i))
        for (i2 <- usedVar2(i))
          token += ((i, i2) -> (token(i, i2) - 1))

    /**
     *
     * @param i
     * @return true if instruction is ready to fire
     */
    def isReady(i: String) = defI.contains(i) && noTokenOutput(i) && oneTokenEveryInput(i) && muI2(i).size > 0

    /**
     *
     * @param i
     * if ready, put instruction in priority queue
     */
    def checkReadiness(i: String): Unit = {
      if (isReady(i) && defI.contains(i))
        readyInstr += i
    }

    def init() = {
      //send token to input instructions
      for (p <- paramD)
        for (n <- isUsing(p)) {
          inputInstr += n
          token += (n, p) -> tSymbVar(p).locus.density //the number of token is equal to the density.
        }
      for (input <- (inputInstr ++ inputLessInstr))
        checkReadiness(input) //it can happen that instructions have no input
    }

    /**
     *
     * @param i
     * @return get the next muInstruction from the already scheduled list associated to i
     */
    def nextMuInstr(i: String): Instr = {
      val muInstLeft = muI2(i)
      val res = muInstLeft.head
      muI2 += (i -> muInstLeft.tail)
      res
    }

    /**
     *
     * @param l      locus of instruction i
     * @param linput locus of input
     * @param i
     * @return redop do not send token at each firing, it depends on the fanout
     */
    def weSend(l: Locus, linput: Locus, i: String): Boolean =
      if (!l.isTransfer && linput.isTransfer) //We have a reduction op
        if (defI(i).isFolded(tZone))
          (muI2(i).size - 1) % l.fanout == 0
        else (muI2(i).size == 1)
      else true

    /**
     * fire an instruction
     *
     * @param i the instruction
     * @return next muInstr executed from $i
     **/
    def fire(i: Instr): Instr = {
      consumeToken(i.names.head)
      val locus = tSymbVar(i.names.head).locus

      if (inputLessInstr.contains(i.names.head) || {
        val inputLocus = tSymbVar(usedVar2(i.names.head).head).locus
        weSend(locus, inputLocus, i.names.head)
      })
        addSeveralToken(i.names.head, locus)
      nextMuInstr(i.names.head)
    }

    init()
    while (readyInstr.nonEmpty) { //main loop
      val next: Instr = defI(readyInstr.dequeue())
      result = fire(next) :: result
      var neighbors = usedVar2(next.names.head) + next.names.head
      if (isUsing.contains(next.names.head))
        neighbors = neighbors ++ isUsing(next.names.head)
      neighbors.map(checkReadiness(_))
    }
    result.reverse


  }

}