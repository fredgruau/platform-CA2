package compiler

import dataStruc.Align.{compose, invert}
import compiler.AST.{Call, Fundef, Layer2, Read, isCons, isNotRead}
import compiler.Circuit.{AstField, Machine, TabSymb, iTabSymb, iTabSymb2, listOf, newFunName}
import compiler.VarKind.{LayerField, MacroField, ParamD, ParamDR, ParamR, StoredField}
import dataStruc.{Dag, DagInstr, toSet}
import dataStruc.DagInstr.setInputNeighbor
import Instr.{a, affectizeReturn}
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
    new DataProg(newDagis, newFuns ++ funs.map { case (k, v) ⇒ k -> v.macroIfy() }, p.tSymbVar, paramD, paramR)
  }

  /**
   *
   * @return dag of zones. modified dagInstr with the added shift instructions
   *         when cycle constraints are met
   *         for reduce, the muinstruction depend wether the reduced field is folded or not*/
  def zones: (DagInstr, Dag[Zone]) = {
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    //nothing to do fro non macro
    /** used to collect econstraint  generated when aligning */
    val constraints: TabSymb[Constraint] = mutable.HashMap.empty
    val rewrite2 = (i: Instr) => if (i.isTransfer) a(i).align(constraints, p.tSymbVar) else List(i)
    val dagis2: DagInstr = dagis.propagate(rewrite2)
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
   * @param zones
   * @return a first version of muInstructions that does not fold reduction and do not consider  shift
   */

  def muInstr(m: Machine, d: DagInstr, zones: Dag[Zone]): Map[String, List[Instr]] = { //: (Map[String, List[Instr]],TabSymb[InfoNbit[_]] )
    require(isLeafCaLoop)
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    var muIs: iTabSymb2[List[Instr]] = HashMap.empty
    val tZone: Map[String, Zone] = DagInstr.defby(zones.visitedL)
    for (i <- d.visitedL) {
      muIs += a(i).name -> i.unfoldSpace(m, p.tSymbVar, zones, tZone)

    }

    muIs
  }


  def coalesc(muI3: List[Instr], zones: Map[String, Zone],
              defI: Map[String, Instr], tabSymbVar: TabSymb[InfoNbit[_]]) = {
    var tSymbVarScalar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty //stores the name of variables produced by spatial unfolding
    for ((iname, info) <- tabSymbVar) {
      if (defI.contains(iname))
        if (defI(iname).isFolded(zones))
          tSymbVarScalar.addOne(iname -> info.scalarify)
    }
  }

  private def deploy(s: String) = tSymbVar(s).locus.deploy(s)

  def unfoldSpace(m: Machine): DataProg[InfoNbit[_]] = {
    val funs2 = funs.map { case (k, v) => k -> v.unfoldSpace(m) }
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    if (!isLeafCaLoop) return new DataProg(dagis, funs2, p.tSymbVar, paramD, paramR)
    //todo y a du boulot aussi a faire pour les not leaf macro
    val (dagis2: DagInstr, z) = zones //the computation of zones introduces shifted variables
    // therefore it must be done before muInstructions
    val muI = muInstr(m, dagis2, z)
    // print("||||||||||||||||||||||||||||||||||||||||||\n" + muI)
    //print("\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\n" + dagis2)
    //TODO use muI to refine constraints

    z.visitedL.reverse.map(_.pick()) //pick is done starting from the first instruction

    //   print("/////////////////////////////////////////\n" + z)
    val tZone: Map[String, Zone] = DagInstr.defby(z.visitedL)
    val defI: Map[String, Instr] = dagis2.defby
    val (muI2, tSymbScalar, coalesc) = permuteAndFixScheduledMu(muI, dagis2, tZone, defI) // revisit muI 's'reduce when reduced exression is folded


    //   print("|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_\n" + muI2)
    val muI3: List[Affect[_]] = scheduleMuCode(muI2, dagis2, defI).toList.asInstanceOf[List[Affect[_]]]
    // print("|__|__|__|__|__|__|__|__|__|__|__|__|__|__|__|__|__|__|__|__\n" + muI3)
    // println("||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__||__")
    //println(tSymbScalar.toList.grouped(4).map(_.mkString("-")).mkString("\n"))
    // println(coalesc.toList.grouped(4).map(_.mkString("-")).mkString("\n"))
    val muI4 = muI3.map(_.coalesc(coalesc))

    //  print(muI4)
    new DataProg(DagInstr(muI4), funs2, tSymbScalar, paramD.flatMap(deploy(_)), paramR.flatMap(deploy(_)))
  }

  /**
   *
   * @param muI   muInstruction in canonical order grouped per instruction's defined name
   * @param dagis instructions needed to compute
   * @param tZ    zones names
   * @return
   */
  def permuteAndFixScheduledMu(muI: Map[String, List[Instr]], dagis: DagInstr,
                               tZ: Map[String, Zone], defI: Map[String, Instr]) = {
    var newMuI: HashMap[String, List[Instr]] = HashMap.empty
    /** stores the name and type
     * of variables produced by spatial unfolding, after register folding */
    var tSymbScalar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    var coalesc: iTabSymb2[String] = HashMap.empty

    //computes the apropriately permutated list of muInst and stores it in newMui
    def permuteAndFixScheduledMu2(name: String): List[Instr] = {

      val i = defI(name) //instruction
      if (newMuI.contains(name)) return newMuI(name) //muInstruction's new schedule has already been computed
      val permuted: List[Instr] =
        if (a(i).isRedop) foldRedop(a(i))
        else if (i.isV) muI(name) //simplest case
        else if (i.isFolded(tZ))
          if (i.isShift) foldShift(a(i))
          else {
            val s = i.mySchedule(tZ)
            if (s != null) dataStruc.Align.compose2(s, muI(name).toSeq).toList
            else throw (new Exception("problem in aligning on root"))
          }
        else throw (new Exception("look why it is not folded in order to guess what to do"))
      newMuI += name -> permuted;
      //for redop the coalesc mapping is handled simultaneously with the ordering of mu Instructions
      if (!a(i).isRedop) {
        val l = a(i).locus.get
        val names = l.deploy(i.names.head)
        if (i.isFolded(tZ) && tSymbVar(i.names.head).k != ParamR()) {
          for (n <- names)
            coalesc += (n -> i.names.head) //we map
          //we add a single symbol
          tSymbScalar.addOne(i.names.head -> tSymbVar(i.names.head).asInstanceOf[InfoNbit[_]].scalarify)
        }
        else for (n <- names) //no coalesced needed
          tSymbScalar.addOne(n -> tSymbVar(i.names.head).asInstanceOf[InfoNbit[_]].scalarify)
      }
      permuted
    }

    def rotateRight[A](seq: Seq[A], i: Int): Seq[A] = {
      val size = seq.size
      seq.drop(size - (i % size)) ++ seq.take(size - (i % size))
    }

    def foldRedop(i: Affect[_]) = {

      val op = a(i).exp.asInstanceOf[ASTL[_, _]].opRedop
      val inputInst = i.inputNeighbors.head
      if (!inputInst.isFolded(tZ)) // we leave as it was, that is to say a single expression
      {
        muI(i.name)
      } // representing the reduction for each component
      else { //for folding of input  to work, the reduction must accumulate
        val l = a(i).locus.get.asInstanceOf[S]
        val d = l.density
        val cpt = Array.fill[Int](d)(0) //used to suffix name
        val result = new Array[Instr](6)
        val names = l.deploy(i.name)
        val iInputMuInsts = muI(inputInst.names.head) //inputNeighbor which is shifted
        val inputShedule: Array[Int] = inputInst.mySchedule(tZ) //schedule of inputNeighbor
        val optionalPrefix =
          if (tSymbVar(i.name).k == ParamR())
            "#Reg"
          else
            ""
        for (j <- 0 to 5) {
          val numI = l.proj(inputShedule(j)) //numwI select the target component of the simplicial vector produced by redop

          val iInputMuInst: Instr = iInputMuInsts(inputShedule(j)) //muInst read
          val nameOfAffectedPrevious = names(numI) + "#" + cpt(numI)
          cpt(numI) += 1;
          val nameOfAffectedNow = names(numI) +
            (if (cpt(numI) * d >= 6) "" //last affected component does no get an integer prefix
            else "#" + cpt(numI))
          val coalescedName = (if (i.isFolded(tZ) || i.isV) i.name else names(numI)) + (if (cpt(numI) * d >= 6) "" else optionalPrefix)

          coalesc += (nameOfAffectedNow -> coalescedName)
          tSymbScalar.addOne(coalescedName -> tSymbVar(i.name).asInstanceOf[InfoNbit[_]].regifyIf(coalescedName != names(numI)))
          val iInputMuInstName = iInputMuInst.names.head
          val readNextMuVar = Instr.readR(iInputMuInstName, repr(iInputMuInst.locus2.get).asInstanceOf[repr[_ <: Ring]])
          val readCurrentRedVar = Instr.readR(nameOfAffectedPrevious, repr(iInputMuInst.locus2.get).asInstanceOf[repr[_ <: Ring]])

          val newMuInstrExp =
            if (cpt(numI) == 1) readNextMuVar //the first myInstruction is a simple affectation
            else Instr.reduceR(readCurrentRedVar, readNextMuVar, //the other apply the binary operator of the muInstruction
              op, repr(iInputMuInst.locus2.get).asInstanceOf[repr[_ <: Ring]])
          result(j) = Affect(nameOfAffectedNow, newMuInstrExp)
        }
        result.toList
      }
    }

    def foldShift(i: Affect[_]) = { //we must have a shift
      assert(i.isShift)
      val muInstUnShift = permuteAndFixScheduledMu2(i.unShifted)
      val (_, List(last)) = muInstUnShift.splitAt(5) //isolate last instruction/we put last instruction first
      //apply same permutation as muInstUnShift
      val Ishifted: Instr = defI(i.unShifted)
      val s2 = Ishifted.mySchedule(tZ)
      val permutedMuShifted = dataStruc.Align.compose2(s2, muI(i.name).toSeq)
      //reste a remplacer lexpression de la premiere affectation de permutedMushifted par l'expression de last
      val inew = Affect(permutedMuShifted(5).names(0), last.exps(0))
      permutedMuShifted(5) = inew
      val res = rotateRight(permutedMuShifted, 1).toList
      res
    }

    for (name <- muI.keys) permuteAndFixScheduledMu2(name)
    (newMuI, tSymbScalar, coalesc)
  }

  /**
   * produce a list of muInstr in the right order.
   *
   * @param muI
   * @param dagis
   */
  def scheduleMuCode(muI: Map[String, List[Instr]], dagis: DagInstr, defI: Map[String, Instr]) = {
    /** which instruction is using this variable */
    var muI2: Map[String, List[Instr]] = muI //HashMap.empty
    //   muI.foreach    {  case (key, muInsts) => muI2 += key->muInsts.reverse    }

    //val defI: Map[String, Instr] = dagis.defby
    val tabInstr = dagis.visitedL.toArray
    var isUsing: HashMap[String, HashSet[String]] = HashMap.empty
    var usedVar2: HashMap[String, HashSet[String]] = HashMap.empty
    var token: HashMap[(String, String), Int] = HashMap.empty
    var priority: HashMap[String, Int] = HashMap.empty
    var inputInstr: HashSet[String] = HashSet.empty
    var inputLessInstr: HashSet[String] = HashSet.empty

    def diff(t2: String) = -priority(t2)

    val readyInstr = new collection.mutable.PriorityQueue[String]()(Ordering.by(diff))
    // x: scala.collection.mutable.PriorityQueue[(Int, Int)] = PriorityQueue()

    //val readyInstr:mutable.PriorityQueue[String]=mutable.PriorityQueue.empty
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

    def noTokenOutput(i: String): Boolean = {
      if (isUsing.contains(i))
        for (i2 <- isUsing(i))
          if (token(i2, i) > 0) return false
      true
    }

    def addToken(i: String, l: Locus): Unit =
      if (isUsing.contains(i))
        for (i2 <- isUsing(i)) {
          val nbToken = Math.max(1, tSymbVar(i2).locus.density / l.density) //if output neigbor has higer density
          token += ((i2, i) -> (token(i2, i) + nbToken))
        }

    def oneTokenEveryInput(i: String): Boolean = {
      if (usedVar2.contains(i))
        for (i2 <- usedVar2(i))
          if (token(i, i2) < 1)
            return false
      return true
    }

    def consumeToken(i: String) =
      if (usedVar2.contains(i))
        for (i2 <- usedVar2(i))
          token += ((i, i2) -> (token(i, i2) - 1))

    def isReady(i: String) = defI.contains(i) && noTokenOutput(i) && oneTokenEveryInput(i) && muI2(i).size > 0

    def checkReadiness(i: String): Unit = {
      if (isReady(i) && defI.contains(i))
        readyInstr += i
    }

    def init() = {
      //send token to input instructions
      for (p <- paramD)
        for (n <- isUsing(p)) {
          inputInstr += n
          token += (n, p) -> tSymbVar(p).locus.density
        }
      for (input <- (inputInstr ++ inputLessInstr))
        checkReadiness(input)
    }

    /**
     *
     * @param i
     * @return
     */
    def nextMuInstr(i: String): Instr = {
      val muInstLeft = muI2(i)
      val res = muInstLeft.head
      muI2 += (i -> muInstLeft.tail)
      res
    }

    def weSend(l: Locus, li: Locus, i: String): Boolean =
      if (!l.isTransfer && li.isTransfer) //We have a redop
        return (muI2(i).size - 1) % tSymbVar(i).locus.fanout == 0
      else return true

    def fire(i: Instr): Instr = {
      consumeToken(i.names.head)
      val locus = tSymbVar(i.names.head).locus

      if (inputLessInstr.contains(i.names.head) || {
        val inputLocus = tSymbVar(usedVar2(i.names.head).head).locus
        weSend(locus, inputLocus, i.names.head)
      })
        addToken(i.names.head, locus)
      nextMuInstr(i.names.head)
    }

    init()
    while (readyInstr.nonEmpty) {
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