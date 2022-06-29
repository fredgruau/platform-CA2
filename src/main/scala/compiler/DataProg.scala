package compiler

import ASTB._
import dataStruc.Align.{compose, invert}
import AST.{Call, Fundef, Layer, Read, isCons, isNotRead, AstPred}
import Circuit.{AstField, Machine, TabSymb, iTabSymb, iTabSymb2, listOf, newFunName}
import VarKind.{LayerField, MacroField, ParamD, ParamDR, ParamR, StoredField}
import dataStruc.{Align, Dag, DagInstr, WiredInOut, toSet}
import dataStruc.WiredInOut.{defby, setInputNeighbor}
import Instr.{a, affectizeReturn}
import ASTB.Tminus1
import ASTBfun.{ASTBg, Fundef2R, redop}
import ASTL.ASTLg

import scala.collection.{Iterable, IterableOnce, Set, immutable, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import scala.language.postfixOps

object DataProg {
  /** pring a map on several small lines, instead of one big line */
  private def string[T](t: TabSymb[T], s: String): String = t.toList.grouped(4).map(_.mkString(s)).mkString("\n") + "\n"

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
    /**
     *
     * @param l list of newly visited  AST Nodes
     * @return elements of $l which are layers.
     */
    def getLayers(l: List[AST[_]]) = l.collect { case la: Layer[_] => la }

    def getSysInstr(l: List[AST[_]]): List[CallProc] = getLayers(l).flatMap(_.systInstr)

    //TODO build the layer structure here, exploit that we have it!
    val dag: Dag[AST[_]] = Dag()
    /** f.body  is the expression containing the value returned by the functions.
     * It  is the  access point to all the AST nodes needed to compute the function.
     * We use a fake call to a macro called "return" to represent the function's code */
    val main = CallProc("return", List(), List(f.body))
    /** contains the current instructions to be explored for retrieving new DagNodes */
    var instrsCur = List(main)
    /** contains the current instructions to be explored for retrieving new DagNodes */
    var layers: List[Layer[_]] = List()
    //  var callProcs: List[List[CallProc]] = List()

    do try {
      val l: List[Layer[_]] = getLayers(dag.addGreaterOf(instrsCur.flatMap(_.exps)))
      layers :::= l;
      instrsCur = (l.flatMap(_.systInstr)) //as we add generators, we possibly get new call to Display debug or memorize
    }
    catch {
      case e@(_: dag.CycleException) =>
        dataStruc.Name.setName(f, "") //permet d'afficher les noms de variables du cycle et donc de
        //  Plus facilement identifier ou se trouve le cycle dans le programme
        for (a <- e.cycle)
          print(a + (if (a.name != null) (a.name + "-") else "-"))
        throw new dag.CycleException(Vector.empty)
    }
    while (!instrsCur.isEmpty)

    dataStruc.Name.setName(f, ""); //for ''grad'' to appear as a name, it should be a field of an object extending the fundef.
    val funs: iTabSymb[Fundef[_]] = immutable.HashMap.empty ++ dag.visitedL.collect { case l: Call[_] => (l.f.name, l.f) }
    /** second  gathering of SysInstr which can now access  the layer's name, because  setName has been called   */
    val instrs = main :: getSysInstr(dag.visitedL)
    /** Symbol table  */
    val t2: TabSymb[InfoType[_]] = mutable.HashMap.empty
    t2 ++= f.p.toList.map(a => ("p" + a.name, InfoType(a, ParamD()))) // stores parameters  in the symbol table.
    t2 ++= layers.map(a => (AST.lify(a.name), InfoType(a, LayerField(a.nbit)))) // stores layers with bit size, in the symbol table.

    new DataProg[InfoType[_]](new DagInstr(instrs, dag), funs.map { case (k, v) ⇒ k -> DataProg(v) },
      t2, f.p.toList.map("p" + _.name), List())
  }

  def nbSpace(u: Option[Locus]) = u match {
    case None => 2
    case Some(V()) => 0
    case Some(E()) => 3
    case Some(F()) => 5
    case Some(T(_, _)) => 9
  }
}

/**
 * Contains the compiled data, and all the functions used to implement the stage of compilation:
 * treify, procedurify, bitify, macroify, foldRegister, unfoldSpace
 *
 * @param dagis the dag of instructions stored in reversed order.
 * @param funs  the macros
 * @tparam U type of the info stored
 * @param tSymbVar symbol table
 * @param paramD   names of data parameters, provides  an order on them
 * @param paramR   names of result parameters , provides  an order on them
 * @param coalesc  coalesced form for identifiers which are regrouped.
 */
class DataProg[U <: InfoType[_]](val dagis: DagInstr, val funs: iTabSymb[DataProg[U]], val tSymbVar: TabSymb[U],
                                 val paramD: List[String], val paramR: List[String], val coalesc: iTabSymb[String] = HashMap.empty) {

  /** look up the symbol table if not found, take the coalesced form */
  def tSymbVarSafe(str: String) = {
    if (!tSymbVar.contains(str) && (!coalesc.contains(str) || !tSymbVar.contains(coalesc(str))))
      throw new Exception("on trouve pas " + str)
    tSymbVar.getOrElse(str, tSymbVar(coalesc(str)))
  }


  override def toString: String = {

    /** returns the number of space tabulation at which to start display the instruction.  */
    def nbSpace2(str: List[String]) = if (str.nonEmpty) DataProg.nbSpace(tSymbVarSafe(str(0)).locusOption) else 1

    val instrs = dagis.visitedL.reverse //if (coales.isEmpty) .map(_.asInstanceOf[Affect[_]].coalesc(coales))
    val instrPrint = instrs.map((i: Instr) =>
      i.toString(nbSpace2(i.names)) + "\n").mkString("")
    (if (isLeafCaLoop) "leaf CA loop: " else "main ") + paramD.mkString(" ") + "=>" + paramR.mkString(" ") + "\n" +
      // (if (coales.isEmpty) dagis else dagis )+//.visitedL.map(_.asInstanceOf[Affect[_]].coalesc(coales)).reverse
      "there is now " + dagis.visitedL.length + "instructions\n" +
      instrPrint +
      tSymbVar.size + " variables:\n " +
      tSymbVar.toList.grouped(4).map(_.mkString("-")).mkString("\n") + "\n\n" +
      (if (coalesc.isEmpty) "" else coalesc.toList.grouped(4).map(_.mkString("-")).mkString("\n")) +
      listOf(funs).mkString("\n \n  ") +
      "\n\n\n"
  }

  /** add new symbol created through affectize */
  private def updateTsymb[U](l: List[AST[_]], v: VarKind): mutable.Map[String, InfoType[_]] =
    tSymbVar.asInstanceOf[TabSymb[InfoType[_]]] ++= l.map((e: AST[_]) => (e.name, new InfoType(e.mym.name, v)))

  /** add new symbol created through affectize with number of bits */
  private def updateTsymbNbit[U](l: List[AST[_]], v: VarKind, g: CodeGen): mutable.Map[String, InfoNbit[_]] = {
    val emptyEnv: HashMap[String, ASTBt[B]] = HashMap.empty[String, ASTBt[B]]
    tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]] ++= l.map((e: AST[_]) =>
      (e.name, new InfoNbit(e.mym.name, v, e.asInstanceOf[ASTBt[_]].nBit(g, emptyEnv))))
  }


  /**
   * @return the DAG of AST becomes a forest of tree, and we we build a Dag of Instructions instead which include.
   *         1- as before callProc to  -1 return    2-show 3 -bug- 4 memo (affectation )
   *         2- pure affectation of AST used two times or more.
   *         variable for those affectation are created with VarKind "Field"
   *         Delayed Constructors are removed from Expressions
   *         Param are replaced by Read with the letter 'p' added to the name
   *         Layers are replaced by Read with the letter 'll' added to the name
   *         Some of the node do not have name, i.e. their name is null
   *         they are not used two times, they did not received a name
   *
   *         * works  for ASTBt instead of ASTLt when setting dagdag to false
   *         which result in directy working on visitedL feature of DAG instead of reconstructing it
   *         it include then with the following difference:
   *         * we compute a new name only for expression used twice, and we certainly
   *         * do not try to optimize the name, we also have to forget about shift when computing inputNeighbors,
   *         * so as to be able to used it in order to insert the new affect at the right place.
   *
   */
  def treeIfy(dagdag: Boolean = true): DataProg[U] = {
    //val p = this.asInstanceOf[DataProg[InfoType[_]]]

    val iT2 = dagis.inputTwice
    val iT1 = iT2.filter(isNotRead) //we could filter out more stuff because it consumes register and registers are a precious ressource
    val iT = iT1.filter(_.isNotTm1Read)
    val dagis2 = dagis.affectIfy(iT1, dagdag) //also replaces access to data parameters+layers by read
    //expression of the Affectation generated are stored in dagis.newAffect, they correspond precisely to nonGenerators.
    val (layerFields, macroFields) = dagis.newAffect.map(_.exp).partition(isLayerFieldE(_))
    if (dagdag) {
      updateTsymb(macroFields, MacroField())
      // when a variable is used twice it should be evaluated in a macro
      //which means its type should be set to MacroFieldk, but carefull, we should provide the number of bits if affectify happen after unfold int.
      updateTsymb(layerFields, StoredField()) //This is excepted for affectation of the form dist<-lldist,
    }
    else {
      val g = new CodeGen(tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]], coalesc)
      updateTsymbNbit(macroFields, MacroField(), g)
      updateTsymbNbit(layerFields, StoredField(), g)
    }

    // the type of dist is set to storedLayer
    // paramD varkind  could  be replaced by Affect , but this should not happen because of the added letter 'p' for the parameter.
    // if a parameter is used two times, the generated affectation will generate a read without the 'p'
    new DataProg(dagis2, funs.map { case (k, v) ⇒ k -> v.treeIfy(dagdag) }, tSymbVar, paramD, paramR, coalesc)
  }

  /** paramD read two times will be affectized we need to check than on loop-macro produced by macroified */
  def treeIfyParam(dagdag: Boolean = true): DataProg[U] = {
    //val p = this.asInstanceOf[DataProg[InfoType[_]]]
    def addpletter(a: AST[_]) = {
      a.name = "p" + a.asInstanceOf[Read[_]].which
    }

    val isNotReadOrParam: AstPred = {
      case r@AST.Read(_) =>
        tSymbVar(r.which).k == ParamD();
      case _ => true
    }
    val isReadAndParam: AstPred = {
      case r@AST.Read(_) =>
        tSymbVar(r.which).k == ParamD();
      case _ => false
    }
    val iT2 = dagis.inputTwice
    val iT1 = iT2.filter(isNotReadOrParam) //we could filter out more stuff because it consumes register and registers are a precious ressource
    val iT = iT1.filter(_.isNotTm1Read)
    //val paramToBeRepl: List[AST[_]] = dagis.dagAst.visitedL.filter(isReadAndParam);
    val paramToBeRepl: List[AST[_]] = dagis.visitedL.flatMap(_.exps(0).leaves()).filter(isReadAndParam); //we scan the leaves because if we scan dagAst, we will touch only a subset of leaves.
    paramToBeRepl.map(addpletter(_));
    val dagis2 = dagis.affectIfy(iT1, dagdag) //also replaces access to data parameters+layers by read
    //expression of the Affectation generated are stored in dagis.newAffect, they correspond precisely to nonGenerators.
    val (layerFields, macroFields) = dagis.newAffect.map(_.exp).partition(isLayerFieldE(_))
    if (dagdag) {
      updateTsymb(macroFields, MacroField())
      for (name <- paramToBeRepl.map(_.name)) {
        val info = tSymbVar(name.drop(1)).asInstanceOf[InfoNbit[_]] //we drop the letter "p" we get the number of bits
        val newInfo = new InfoNbit(info.t, MacroField(), info.nb)
        tSymbVar.addOne(name -> newInfo.asInstanceOf[U])
      }

      // when a variable is used twice it should be evaluated in a macro
      //which means its type should be set to MacroFieldk, but carefull, we should provide the number of bits if affectify happen after unfold int.
      updateTsymb(layerFields, StoredField()) //This is excepted for affectation of the form dist<-lldist,
    }
    else {
      val g = new CodeGen(tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]], coalesc)
      updateTsymbNbit(macroFields, MacroField(), g)
      updateTsymbNbit(layerFields, StoredField(), g)
    }

    // the type of dist is set to storedLayer
    // paramD varkind  could  be replaced by Affect , but this should not happen because of the added letter 'p' for the parameter.
    // if a parameter is used two times, the generated affectation will generate a read without the 'p'
    new DataProg(dagis2, funs.map { case (k, v) ⇒ k -> v.treeIfy(dagdag) }, tSymbVar, paramD, paramR, coalesc)
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
  private def isLeafCaLoop: Boolean = funs.isEmpty &&
    !tSymbVar.valuesIterator.exists(_.k.isStoredField)

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
      val newDataProg = new DataProg(newDagis, mutable.HashMap.empty, newtSymbVar, fparamDwithoutR, fparamRname).treeIfyParam()
      newDataProg //the parameter needs to be treeified
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
    //  print("ererererererererererererererererererererererererererererererererererererererererererererer\n" + dagis2)
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
    val zoneDag: Dag[Zone] = dagis2.quotient(proximity2, transform)
    zoneDag.visitedL.map(_.addPartitionOut()) //set partition constraints towards output neighbors
    //now we know if the TCC will fold, before we pick, we could try to further constrain the cycle so as to reuse
    //delayed variables in order to avoid introducing new registers
    zoneDag.visitedL.map(_.setFoldConstrSimplicial())
    (dagis2, zoneDag)
  }


  /**
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
      return new DataProg(DagInstr(muI.reverse), funs2, tSymbScalar, paramD.flatMap(deploy(_)), paramR.flatMap(deploy(_)))
    }
    val dagis1bis = addParamRtoDagis(dagis) //add a new paramR after redop which is done in a  macroField todo avoid recomputing the whole dag
    val (dagis2: DagInstr, z: Dag[Zone]) = zones(dagis1bis) //the computation of zones introduces shifted variables
    // therefore it must be done before muInstructions
    val muI = muInstr(m, dagis2) //TODO inspect muI's tm1 to refine constraints so as to fold vortex
    z.visitedL.reverse.map(_.pick()) //pick is done starting from the first instruction
    val tZone: Map[String, Zone] = defby(z.visitedL)
    // print(tZone)
    val defI: Map[String, Instr] = dagis2.defby
    val (muI2, tSymbScalar, coalesc) = permuteAndFixScheduledMu(muI, dagis2, tZone, defI) // revisit muI 's'reduce when reduced exression is folded
    //we separate the reduction in two parts: one that can do at tm1 and the rest that is done now.
    val muI3: List[Affect[_]] = scheduleMuCode(muI2, dagis2, defI, tZone).toList.asInstanceOf[List[Affect[_]]]
    val iT = DagInstr(muI3).inputTwice.filter(isNotRead) //we exploit the DAG form to find out about usedTwice exp, we did not used it yet!!!
    //if the factorized expression is just a << or >> as it is now ?? we better just recompute it
    //print("____|____|____|____|____|____|____|____|____|____|____|____|\n"+muI3)  //printing this for debug is usefull because we see which component is processed
    val muI4 = muI3.map(_.coalesc(coalesc))
    //adds paramD to symbol Table WITH the suffx for specifying direction, since paramD will be deployed.
    //paramR are also deployed but their case is already  handled correctly in the symboltable
    for ((name, info: InfoNbit[_]) <- p.tSymbVar)
      if (info.k == ParamD()) {
        for (nameWithSufx <- deploy(name))
          tSymbScalar.addOne(nameWithSufx -> info.scalarify)
        if (info.locus != V()) //the prior infoTab must be removed from the symbol Table, for V there is no suffixes, this is why it is special
        tSymbScalar.remove(name)
      }
    new DataProg(DagInstr(muI3), funs2, tSymbScalar, paramD.flatMap(deploy(_)), paramR.map(addsAnR(_)).flatMap(deploy(_)), coalesc)
  }

  /**
   *
   * @param muI   muInstruction in canonical order grouped per instruction's defined name
   * @param dagis instructions needed to compute
   * @param tZ    zones names
   * @return hashmap of muInst associated to inst, now scheduled between the 6
   */
  def permuteAndFixScheduledMu(muI: Map[String, List[Instr]], dagis: DagInstr,
                               tZ: Map[String, Zone], defI: Map[String, Instr]): (HashMap[String, List[Instr]], TabSymb[InfoNbit[_]], iTabSymb[String]) = {
    var oldmuI = muI //it will be modified to remove the tm when doing reduction
    var newMuI: HashMap[String, List[Instr]] = HashMap.empty
    /** stores the name and type of variables produced by spatial unfolding, after register folding */
    var tSymbScalar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    /** stores a mapping to coalesced registers    */
    var coalesc: iTabSymb[String] = HashMap.empty

    /**
     *
     * @param name variable affected by an instruction
     * @return muInstVector  associated to instr, now scheduled
     *
     */
    def permuteAndFixScheduledMu2(name: String): List[Instr] = {
      if (!defI.contains(name))
        throw new Exception("pas trouvé" + name)
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
            (if (iInputMuInstOrdered(j).exps(0).asInstanceOf[ASTBt[_]].isTm1) 1 else 0)
        val isTm1 = iInputMuInstOrdered.map(_.exps.head.asInstanceOf[ASTBt[_]].isTm1)
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
            val tm1Opt = if (isTm1(j)) "tm1" else "" //suffixe optionnel a rajouter
            val nameOfAffectedPrevious = names(numI) + tm1Opt + "#" + cptt
            if (isTm1(j)) cptTm1(numI) += 1 else cpt(numI) += 1;
            val onlyTm1 = tm1Sum(numI) * d == 6
            val onlyTm1Last = onlyTm1 && cptTm1(numI) == tm1Sum(numI) //true for final reduction when only tm1
            val firstNonTm1 = (cpt(numI) == 1) && !(isTm1(j))
            val lastNonTm1 = ((cpt(numI) + tm1Sum(numI)) * d == 6) && (!isTm1(j)) // representing the reduction for each component
            val lastTm1 = (cptTm1(numI) == tm1Sum(numI)) && (isTm1(j)) // representing the reduction for each component
            val nameOfAffectedNow = names(numI) + (if (onlyTm1 && lastTm1) "" else //when there is only tm1 then the last term has no prefix
              (tm1Opt +
                (if (lastNonTm1) "" else ("#" + (cptt + 1))) //last affected component does no get an integer prefix
                ))
            val coalescedName = if (i.isFolded(tZ) || i.isV) i.name else names(numI)
            val coalescedNameTm1 = coalescedName + (if (!onlyTm1Last) tm1Opt else "") //precise the name by adding "tm1"
            coalesc += (nameOfAffectedNow -> coalescedNameTm1)
            tSymbScalar.addOne(coalescedNameTm1 -> tSymbVar(i.name).asInstanceOf[InfoNbit[_]]) //.regifyIf(coalescedName != names(numI)))

            val readNextMuVar = Instr.readR(iInputMuInstName, r)
            val nameOfFinalAffectedTm1 = names(numI) + "tm1" + "#" + tm1Sum(numI)
            //iInputMuInstOrdered(scheduleOfLastAffectedTm1).names.head+"tm1#" + nbDelayed
            val readCurrentRedVar =
              if (firstNonTm1) //we retrieve the other sum using a tm1, it introduces another Z variable, to be removed later
              ASTB.tm1(Instr.readR(nameOfFinalAffectedTm1, r))(r)
              else
              Instr.readR(nameOfAffectedPrevious, r)
            val newMuInstrExp =
              if (cptTm1(numI) == 1 && isTm1(j)) readNextMuVar //the first myInstruction is a simple affectation
              else Instr.reduceR(readCurrentRedVar, readNextMuVar, //the other apply the binary operator of the muInstruction
                op.asInstanceOf[redop[Ring]], r)
            val newMuInstrExpTm1 = if (onlyTm1Last) ASTB.tm1(newMuInstrExp)(r) else newMuInstrExp
            result(j) = Affect(nameOfAffectedNow, newMuInstrExpTm1)
          }
        }
        result.toList
      }
    }

    /**
     *
     * @param i shifting instruction
     * @return muInstr generated from a shift are computed using specific processing implementing a rotation from the unshifted
     */
    def foldShift(i: Affect[_]) = {
      assert(i.isShift) //i must be a shift
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
   * shift instruction receives a special processing
   * 1- they exchange priority with the shifted instruction, in order to be scheduled first
   * 2- they supress the shifted instruction from their input neighors, in order to schedulable first
   * 3- they add the input neighbors of the schifted instruction, so as not to be scheduled too early.
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
    /** token betweens the  two instructions setting the two variables */
    var token: HashMap[(String, String), Int] = HashMap.empty
    var priority: HashMap[String, Int] = HashMap.empty
    var shifts: HashSet[String] = HashSet.empty
    var inputInstr: HashSet[String] = HashSet.empty
    var inputLessInstr: HashSet[String] = HashSet.empty

    def diff(t2: String) = -priority(t2)

    val readyInstr = new collection.mutable.PriorityQueue[String]()(Ordering.by(diff))
    var prio = 0
    var result: List[Instr] = List()
    for (i <- dagis.visitedL) { //initalise the vars: usedVar2,priority,
      var u = i.usedVars()
      //for shifttoto instruction we must add used(toto) to used (shiftToto) because shiftToto will use the same variable as toto
      if (i.isShift) {
        u /*++=*/ = defI(i.names.head.drop(5)).usedVars()
        shifts += i.names.head
      }
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

    def permutePrioShiftWithShifted = {
      for (s <- shifts) {
        val p = priority(s)
        val shifted = s.drop(5)
        priority += s -> priority(shifted)
        priority += shifted -> p
        val u = 1
      }
    }
    //permutePrioShiftWithShifted
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
      {
        if (defI(i).isFolded(tZone))
          (muI2(i).size - 1) % l.fanout == 0
        else (muI2(i).size == 1)
      }
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
    /* if (shifts.nonEmpty)
       print("rer")*/
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

  def coalesc2(str: String) = coalesc.getOrElse(str, str)

  /** if an id x is used a single time, remplace read(x) by its expression.
   * This applies in particular, for transfer happenning just before reduction */
  def simplify(): DataProg[InfoType[_]] = {
    val nInstrBeforeSimplif = dagis.visitedL.size
    val p = this.asInstanceOf[DataProg[InfoType[_]]]
    val newTsymbar = p.tSymbVar
    if (isLeafCaLoop) {
      val uO: List[Instr] = p.dagis.usedOnce()
      val uOnames1: Predef.Set[String] = uO.map(_.names(0)).toSet
      val uOnames = checkIfRedefined(uOnames1)
      var defs: Map[String, Instr] = defby(dagis.visitedL)
      val newVisitedL = dagis.visitedL.reverse.map((f: Instr) =>
        if (f.inputNeighbors.map(_.names(0)).toSet.intersect(uOnames).nonEmpty) //f contains some read to be replaced
        {
          val a = new Affect(f.names(0), defs(f.names(0)).exps(0).asInstanceOf[ASTBt[_]].simplify(uOnames, defs))
          defs = (defs + (f.names(0) -> a)) // we update the defs as it might be reused on the fly when we replace a read in an expression which itself will replace another read.      a
          a
        }
        else f
      )
      dagis.visitedL = newVisitedL.reverse.filter((i: Instr) => !uOnames.contains(i.names(0))) //removes the now useless instructions
      WiredInOut.setInputAndOutputNeighbor(dagis.visitedL)
      val nameStillUsed = p.dagis.visitedL.flatMap(_.names).toSet.diff(uOnames)
      val coalescedStillUsed = nameStillUsed.map((str: String) => coalesc.getOrElse(str, str))
      for (str <- newTsymbar.keys) //we remove from the table the now useless symbols
        if (!coalescedStillUsed.contains(str) && !(newTsymbar(str).k == ParamD()))
          newTsymbar.remove(str)
      //dagis.visitedL.map(_.asInstanceOf[Affect[_]].correctName())
      if (dagis.visitedL.size < nInstrBeforeSimplif) simplify() //simplification can enable more simplification!

    }
    new DataProg(dagis, funs.map { case (k, v) ⇒ k -> v.simplify }, newTsymbar, paramD, paramR, coalesc)
  }


  /** computes a map reInsertionC(nom) if defined it is instruction that should be moved before nom->exp
   * tm1 of an exression using many variables R1<-tm1(exp(R2,... Rn)
   * Rule C; when going towards first instruction, meet one and exactly one affectation for each Ri, i>1, without R1 being used
   * When going towards last instruction, no redefinition of any of the RI
   * R2,..RN  are defined a single time globally we identify that by checking that is not a key of coales.
   * Algo: we maintain the set of Ris still to be met, we also keep the original set.
   * */
  private def movesOfRuleC(instrs: List[Instr]) = {
    var reInsertionC: HashMap[String, String] = HashMap()
    var toBeMet: HashMap[String, Set[String]] = HashMap()

    //it suffices to start by a tm1 (we consider  a simple property) and have name not coalesced
    def checkRuleC(i: Instr, used: Set[String]) = (
      i.exps(0).asInstanceOf[ASTBg].isTm1 && used.intersect(coalesc.keys.toSet).isEmpty)

    for (instr <- instrs) {
      var nom = instr.names(0)
      val u: Set[String] = instr.usedVars()
      if (checkRuleC(instr, u)) {
        toBeMet = toBeMet + (nom -> u)
      }
      for (m <- toBeMet) {
        if (u.contains(m._1))
          toBeMet -= m._1 //case closed negatively
        if (m._2.contains(nom)) {
          if (toBeMet(m._1).contains((nom))) {
            val newToBeMet = toBeMet(m._1) - nom
            if (newToBeMet.isEmpty) {
              toBeMet -= m._1 //case closed positively
              reInsertionC += (nom -> m._1) //record sucess and where to move
            }
            else toBeMet += (m._1 -> newToBeMet)
          }
        }
      }
    }
    reInsertionC
  }

  /**
   *
   * @param reInsertion target is name of instruction to be moved; source is name of instruction where to insert
   * @param instrs
   * @return
   */
  private def detmANDmove(reInsertion: Map[String, String], instrs: List[Instr]) = {
    var tobeMoved: iTabSymb[Instr] = HashMap()
    instrs.flatMap(
      (instr: Instr) => {
        val nom = instr.names(0)
        if (reInsertion.values.toSet.contains(nom)) {
          tobeMoved += (nom -> instr.detm1iseR);
          List()
        }
        else {
          var resu = List(instr)
          if (reInsertion.keys.toSet.contains(nom))
            resu ::= tobeMoved(reInsertion(nom))
          resu.reverse
        }

      })
  }

  /** sub expression of $e$ with tm1s inside */
  private def tm1s(e: AST[_]) = {
    val d = new Dag[AST[_]](List(e))
    d.visitedL.filter(_.asInstanceOf[ASTBt[_]].isTm1)
  }

  /** returns instruction with a single tm1 of the form tm1(variable) */
  private def instrsWithaTm1Reg(instrs: List[Instr]) = {
    var result: HashMap[String, String] = HashMap()
    for (instr <- instrs) {
      val theTm1s = tm1s(instr.exps(0))
      if (theTm1s.size > 1) throw new Exception("Dammed, there is two possible tm1 for this affect")
      for (e <- theTm1s)
        e.inputNeighbors(0) match {
          case r@Read(_) =>
            if (result.contains(instr.names(0))) throw new Exception("there is two possible tm1(Rx) for this R1")
            result += (instr.names(0) -> r.which)
          case _ =>
        }
    }
    result
  }

  /**
   * @return tm1 of a single register R1<-exp ...tm1(R2),
   *         //rule A    if R2 is not affected before the instruction ==> the tm1 is simply supressed.
   *         // rule B   if R1 is not affected before the instruction
   *         //      and R2 is not affected after the instruction, until last R1's use ==> move the instruction after last R1's use
   * @param candReg
   * @param instrs
   */
  private def ruleAandB(candReg: Map[String, String], instrs: List[Instr]) = {
    var candA = candReg.keys.toSet //candidR1.keys.toSet //candidate for simplest rule
    var candB = candA //candidate for the second a bit more complex rule
    /** target identifies last instr using source */
    var lastUse: HashMap[String, String] = HashMap()
    /** register which should be redefined */
    var beforeDef: HashSet[String] = HashSet()
    var live: HashSet[String] = HashSet()
    val candBCoalesc = candB.map(coalesc2(_))
    for (instr <- instrs) {
      val nom = instr.names(0)
      if (beforeDef.contains(nom))
        candB -= nom //R1 is re-defined before
      for (r1 <- beforeDef.intersect(candA))
        if (coalesc2(nom) == coalesc2(candReg(r1))) //r2 is redefined before definition of r1         }
        candA -= r1
      val newUsed = instr.usedVars().map(coalesc2(_))
      for (nowUsed <- newUsed.diff(live))
        if (!lastUse.contains(nowUsed))
          lastUse += (nowUsed -> nom)
      live = live.union(candBCoalesc.intersect(newUsed)) //live is a set of coalesced
      for (r1 <- candB)
        if (
          live.contains(coalesc2(r1)) && //R1 will be used
            coalesc2(nom) == coalesc2(candReg(r1))) //after R2 is redefined (now)
        candB -= r1

      if (candA.contains(nom)) { //we just pass the definition candA is still equal to its original value
        live -= coalesc2(nom)
        beforeDef += nom
      }
    }
    candB = candB.diff(candA) //candidates veryfying A and B are hanled as A
    def pred(s: (String, String)) = candB.contains(s._1) //we need a map for candB to know where to move.
    val reInsertionB = lastUse.filter(pred).map(_ swap) //allows to reuse move
    (candA, reInsertionB)
  }

  /** tm1 operator are normaly supressed by adding registers, nevertheless, different rules can be applied to avoid the cost
   * of adding register:  , juste removing the tm1 (rule A)
   * moving the instruction forward (rule B) or backward.(rule C) *adding a store instruction (rule D) */
  def detm1Ify(): DataProg[InfoType[_]] = {
    def isParamR(str: String) = tSymbVarSafe(str).k == ParamR()

    val p = this.asInstanceOf[DataProg[InfoType[_]]]
    if (isLeafCaLoop) {


      //computes candidates R1s and their associated R2

      /** lastUse(x)=instruction where x was used last if x is in cand2, x=exp should be inserted after lastuse(x) */

      /*     var candidR1: HashMap[String, String] = HashMap()
           for (instr <- p.dagis.visitedL) {
             for (e <- tm1s(instr.exps(0)))
               e.inputNeighbors(0) match {
                 case r@Read(_) =>
                   if (candidR1.contains(instr.names(0))) throw new Exception("there is two possible tm1(R2) for this R1")
                   candidR1 += (instr.names(0) -> r.which)
                 case _ =>
               }
           }*/
      val candReg = instrsWithaTm1Reg(p.dagis.visitedL)
      /*      var candA = candReg.keys.toSet//candidR1.keys.toSet //candidate for simplest rule
            var candB = candA //candidate for the second a bit more complex rule
            /** register which should be redefined */
            var beforeDef: HashSet[String] = HashSet()
            var live: HashSet[String] = HashSet()
            val candBCoalesc = candB.map(coalesc2(_))
            for (instr <- p.dagis.visitedL) {
              val nom = instr.names(0)
              if (beforeDef.contains(nom))
                candB -= nom //R1 is re-defined before
              for (r1 <- beforeDef.intersect(candA))
                if (coalesc2(nom) == coalesc2(candidR1(r1))) //r2 is redefined before definition of r1         }
                candA -= r1
              val newUsed = instr.usedVars().map(coalesc2(_))
              for (nowUsed <- newUsed.diff(live))
                if (!lastUse.contains(nowUsed))
                  lastUse += (nowUsed -> nom)
              live = live.union(candBCoalesc.intersect(newUsed)) //live is a set of coalesced
              for (r1 <- candB)
                if (
                  live.contains(coalesc2(r1)) && //R1 will be used
                    coalesc2(nom) == coalesc2(candidR1(r1))) //after R2 is redefined (now)
                candB -= r1

              if (candA.contains(nom)) { //we just pass the definition candA is still equal to its original value
                live -= coalesc2(nom)
                beforeDef += nom
              }
            }

            candB = candB.diff(candA) //candidates veryfying A and B are hanled as A

            */
      val (candA, reInsertionB) = ruleAandB(candReg, p.dagis.visitedL)

      //we now  remove tm1s, from candA
      p.dagis.visitedL = p.dagis.visitedL.map(
        (instr: Instr) => if (candA.contains(instr.names(0))) instr.detm1iseR else instr
      )

      //we now  remove tm1s, and move instructions from candB
      p.dagis.visitedL = detmANDmove(reInsertionB, p.dagis.visitedL.reverse).reverse


      val reInsertionC = movesOfRuleC(p.dagis.visitedL)
      p.dagis.visitedL = detmANDmove(reInsertionC, p.dagis.visitedL)

      //Rule D;  replace affect (paramD,tm1(exp) by store(paramD,-1,exp)
      p.dagis.visitedL = p.dagis.visitedL.map((instr: Instr) =>
        if (isParamR(instr.names(0)))
          instr.asInstanceOf[Affect[_]].toStoreDetmise()
        else instr
      )

      //for the tm1 that could not be supressed we now proceed to standard detmify through creation of new registers which means new affectation.
      val toBeRepl: Set[AST[_]] = toSet(p.dagis.dagAst.visitedL.filter(_.asInstanceOf[ASTBt[_]].isTm1)) //we could filter out more stuff because it consumes register and registers are a precious ressourcefor(e<-toBeRepl)
      //we check that there is no tm1 in tm1
      for (e <- toBeRepl) {
        val d = (new Dag[AST[_]](List(e.inputNeighbors(0)))) //builds the dag of tm1's expr in order to see if itself contains other tm1
        assert(d.visitedL.filter(_.asInstanceOf[ASTBt[_]].isTm1).isEmpty) //finally we prefer to hypotheses there are no tm1s in tm1q
      }
      dagis.deTm1fy(toBeRepl.asInstanceOf[immutable.Set[ASTBt[_]]])
      val macroFields = dagis.newAffect.map(_.exp)
      // p.updateTsymb( macroFields, MacroField()) // when a variable is used twice it should be evaluated in a macro

      val g = new CodeGen(tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]], coalesc)
      updateTsymbNbit(macroFields, MacroField(), g)
      val u = 1

    }
    new DataProg(dagis, funs.map { case (k, v) ⇒ k -> v.detm1Ify() }, p.tSymbVar, paramD, paramR, coalesc)
  }

  /** do not simplify variable $v$used once, if register (coalec) used for computing $v$ is redefined before $v$ is used */
  def checkIfRedefined(candidateSimplif: Predef.Set[String]): Predef.Set[String] = {
    /** contains variables whose declaration have been visited, but whose use not yet visited */
    var allUsed: HashMap[String, Predef.Set[String]] = HashMap()
    var live: Predef.Set[String] = HashSet()
    var result = candidateSimplif
    for (instr <- dagis.visitedL.reverse) {
      val v = instr.names(0)
      val used = instr.usedVars()
      allUsed += v -> used //we remember variable used for a given ide
      for (u <- used) {
        live -= u; //we know they are used once
      }
      for (l <- live) { //look for redefinition of a register used by l before single use of l
        var cancel = false
        for (usedByl <- allUsed(l))
          if (coalesc2(usedByl) == coalesc2(v)) //we look if l uses a variable that coalesc like v
          cancel = true //if found such variables, we cancel simplification of l
        if (cancel) {
          live -= l
          result -= l //implies not to be simplified
        }
      }
      if (candidateSimplif.contains(v)) live += v;
    }
    result
  }


  def unfoldInt(): DataProg[InfoNbit[_]] = { //todo faut rajouter les stores et peut etre des affect pour marquer la difference
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    if (isLeafCaLoop) {
      val cod = new CodeGen(p.tSymbVar, coalesc)
      for (inst <- dagis.visitedL.reverse) {
        val res = cod.codeGen(inst)
        val res2 = res.map(_.map(_.toStringTree).mkString("|_____|"))
        println("________________\n" + res2.mkString("\n"))
        //print(cod.constant)
      }


    }


    new DataProg(dagis, funs.map { case (k, v) ⇒ k -> v.unfoldInt() }, p.tSymbVar, paramD, paramR, coalesc)
  }
}