package compiler

import compiler.AST.{Call, Fundef, Layer2, isCons, isNotRead}
import compiler.Circuit.{AstField, TabSymb, iTabSymb, listOf, newFunName}
import compiler.VarKind.{MacroField, LayerField, ParamD, ParamDR, ParamR, StoredField}
import dataStruc.{Dag, DagInstr, toSet}
import dataStruc.DagInstr.setInputNeighbor
import Instr.{a, affectizeReturn}
import compiler.Circuit.Machine
import dataStruc.DagNode.components

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
  def apply[T](f: Fundef[T]): DataProg[T, InfoType[_]] = {
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

    new DataProg[T, InfoType[_]](new DagInstr(instrs, dag), funs.map {
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
 * @tparam T type returned by the function //TODO virer T, it is never used for whatever check
 * @tparam U type of the info stored
 * @param tSymbVar symbol table
 * @param paramD   names of data parameters, provides  an order on them
 * @param paramR   names of result parameters , provides  an order on them
 */
class DataProg[+T, U <: InfoType[_]](val dagis: DagInstr, val funs: iTabSymb[DataProg[_, U]], val tSymbVar: TabSymb[U],
                                     val paramD: List[String], val paramR: List[String]) {
  override def toString: String = paramD.mkString(" ") + "=>" + paramR.mkString(" ") + "\n" + dagis +
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
  def treeIfy(): DataProg[T, InfoType[_]] = {
    val p = this.asInstanceOf[DataProg[T, InfoType[_]]]
    val dagis2 = dagis.affectIfy(p.dagis.inputTwice) //also replaces access to data parameters+layers by read
    //expression of the Affectation generated are stored in dagis.newAffect, they correspond precisely to nonGenerators.
    val (layerFields, macroFields) = dagis.newAffect.map(_.exp).partition(isLayerFieldE(_))
    p.updateTsymb(macroFields, MacroField()) // when a variable is used twice it should be evaluated in a macro
    //which means its type should be set to MacroField
    p.updateTsymb(layerFields, StoredField()) //This is excepted for affectation of the form dist<-lldist,
    // the the type of dist is set to storedLayer
    // paramD varkind  could  be replaced by Affect , but this should not happen because of the added letter 'p' for the parameter.
    // if a parameter is used two times, the generated affectation will generate a read without the 'p'
    new DataProg(dagis2, funs.map { case (k, v) ⇒ k -> v.treeIfy() }, p.tSymbVar, paramD, paramR)
  }

  /**
   * @return replaces function call by procedure call
   *         "return " callProc together with Cons expression are replaced by  affectations  to result parameters,
   *         Call AST nodes are replaced by   callProc instructions
   *         x<-Heead y<-Taail are replaced by directly passing x to the call Proc , written as an affectation of x,y
   *         instructions  of the form: id<-tail  id<-head, return   becomes useless. They are filtered out
   *         variable for effective (resp. formal) result are created with VarKind "StoredField" (resp. ParamR)
   */
  def procedurIfy(): DataProg[T, InfoType[_]] = {
    val p = this.asInstanceOf[DataProg[T, InfoType[_]]]
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
  def bitIfy(nbitP: List[Int]): DataProg[_, InfoNbit[_]] = {
    val p = this.asInstanceOf[DataProg[T, InfoType[_]]]
    /** set of expressions being reduced. */
    val redops: HashSet[AST[_]] = HashSet() ++
      dagis.dagAst.visitedL.asInstanceOf[List[ASTLt[_, _]]].flatMap {
        _.redExpr
      }
    /** values being reduced must be id of variable
     * so we affectify those, before bitIfying,
     * because that puts new ids in the symbol table
     * for  which we will also need to know the size */
    val dagis1 = p.dagis.affectIfy(redops(_));
    p.updateTsymb(dagis.newAffect.map(_.exp), MacroField())
    /** We generate also variable which are effective data parameters for called macro
     * their kind is set to StoredField() */
    val effectiveDataParam: HashSet[AST[_]] = HashSet() ++ dagis1.allGenerators.flatMap(
      { case cp@CallProc(p, names, exps) => if (Instr.isProcessedInMacro(p)) List() else exps.filter(isNotRead(_)); case _ => List() })
    val dagis2 = dagis1.affectIfy(effectiveDataParam(_))
    /** effective result parameters which were already variables need to be re-registered as storedFields */
    val newStoredFiedl: List[AST[_]] = effectiveDataParam.toList.filter((a: AST[_]) => AST.isNotRead(a) || p.tSymbVar(a.name).k == MacroField())
    p.updateTsymb(newStoredFiedl, StoredField())
    val nbitExp: AstField[Int] = mutable.HashMap.empty
    val newFuns: TabSymb[DataProg[_, InfoNbit[_]]] = mutable.HashMap.empty
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

  private def isLayerFieldE(e: AST[_]): Boolean = e match {
    case AST.Read(s) => tSymbVar(s).k.isLayerField
    case _ => false
  }

  def macroIfy(): DataProg[T, InfoNbit[_]] = {
    def needStored(s: String): Boolean = tSymbVar(s).k.needStored

    /**
     *
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
    def builtFun(finstrs: Iterable[Instr]): DataProg[_, InfoNbit[_]] = {
      val pureAffect = finstrs.map(_.callProcToAffect)
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

    val p = this.asInstanceOf[DataProg[T, InfoNbit[_]]]
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
    val newFuns: TabSymb[DataProg[_, InfoNbit[_]]] = mutable.HashMap.empty

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
    new DataProg(newDagis, newFuns ++ funs.map { case (k, v) ⇒ k -> v.macroIfy() }, p.tSymbVar, paramD, paramR)
  }

  /**
   *
   * @return computes the offsets of the layers    */

  def foldRegister(offset: Integer): DataProg[_, InfoNbit[_]] = {
    val funs2 = funs.map { case (k, v) ⇒ k -> v.foldRegister(0) }
    val p = this.asInstanceOf[DataProg[T, InfoNbit[_]]]
    //nothing to do fro non macro
    if (!isLeafCaLoop) return new DataProg(dagis, funs2, p.tSymbVar, paramD, paramR)
    /** used to collect econstraint  generated when aligning */
    val constraints: TabSymb[Constraint] = mutable.HashMap.empty
    // dagis.visitedL = dagis.visitedL.map( (i: Instr) => if (i.isTransfer) a(i).align3(constraints) else i)

    val rewrite = (i: Instr) => if (i.isTransfer) a(i).align(constraints) else i
    val dagis2: DagInstr = dagis.propagateUnit(rewrite)
    if (!constraints.isEmpty) println("Constraint: " + constraints) //we check constraints generated
    for (i <- dagis2.visitedL) i.reset //clean stuff being generated when creating macro


    // val notFolded  = mutable.HashSet.empty[String] //we must remember variables that could not be folded.
    /**
     * used to build zone defined as connected components of identical locus: transfer or simplicial
     * we start by target which is the fist component and tries to add source which is the second comonent
     * * second component is source, therefore the first can be callProc*/
    val proximity2: (Instr, Instr) => Boolean =
      (x: Instr, y: Instr) => x.isInstanceOf[CallProc] || x.isTransfer == y.isTransfer

    def transform(g: Iterable[Instr]): List[Zone] = List(Zone(constraints, g.asInstanceOf[Iterable[Affect[_]]]))

    /**
     * We here assume that the zones form a Dag, it could fail, in which case we should look back to the code
     * and see if we can formulate the code differently so as to obtain a Dag
     * a Dag for zones simplifies a lot the comming picking phase
     */
    val zoneDag: Dag[Zone] = dagis2.quotient2(proximity2, transform)
    zoneDag.visitedL.map(_.addPartitionOut()) //set partition constraints towards output neighbors
    zoneDag.visitedL.map(_.setFoldConstrSimplicial())
    zoneDag.visitedL.reverse.map(_.pick())
    print(zoneDag + " ________________________________________________________________________\n")
    new DataProg(dagis, funs2, p.tSymbVar, paramD, paramR)
  }

  def unfoldSpace(m: Machine): DataProg[_, InfoNbit[_]] = {
    val p = this.asInstanceOf[DataProg[T, InfoNbit[_]]]
    val rewrite: Instr => List[Instr] = _.unfoldSpace(m, p.tSymbVar)
    if (isLeafCaLoop) {
      val muInst = p.dagis.visitedL.flatMap(rewrite)
      print(muInst)
    }
    val funs2 = funs.map { case (k, v) => k -> v.unfoldSpace(m) }
    //    val rewrite: Instr => List[Instr] =_.unfoldSpace(m,p.tSymbVar)
    //    val dagis2=if(isLeafCaLoop)p.dagis.propagate(rewrite) else  p.dagis
    new DataProg(dagis, funs2, p.tSymbVar, paramD, paramR)
  }

}