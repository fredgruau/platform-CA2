package compiler

import compiler.AST.{Call, Fundef, Layer2, isCons}
import compiler.Circuit.{AstField, TabSymb, iTabSymb, listOf, newFunName}
import compiler.VarKind.{Field, ParamD, ParamDR, ParamR, StoredField}
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

  /**
   * @param f function to be compiled
   * @tparam T type of result returned by f.
   * @return A dataProg in highly compact forrm with four type of instructions which  are callProc to:
   *         -1 return (for the main)   2-show 3 -bug-4 memo (affectation to the next field for layers)
   *         Expression includes the following constructors:
   *         -1  AST Constructor: Delayed  Param | Call1 Call2 Call3 Coons Heead Taail | Read
   *         -2  ASTL Constructor: Binop  Coonst  Uno Redop  Clock Broadcast Send Transfer Sym
   *         The DFS algo of DAG visits all Delayed node recursively as soon as they are created
   *         Variables with varKind paramD are created
   ***/
  def apply[T](f: Fundef[T]): DataProg[T, InfoType[_]] = {
    def getSysInstr(l: List[AST[_]]): List[CallProc] = l.collect { case la: Layer2[_] => la.systInstrs2 }.flatten

    //TODO build the layer structure here, exploit tthat we have it!
    val dag: Dag[AST[_]] = Dag()
    /** f.body  is the expression containing the value returned by the functions.
     * It  is the  access point to all the AST nodes needed to compute the function.
     * We use a fake call to a macro called "return" to represent the function's code */
    val main = CallProc("return", List(), List(f.body))
    var instrsCur = List(main) //instruction racine de tout
    //as we add generators, we possibly get new call to Display debug or memorize
    do
      try instrsCur = getSysInstr(dag.addGenerators(instrsCur.flatMap(_.exps)))
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
    val funs: iTabSymb[Fundef[_]] = immutable.HashMap.empty ++ dag.visitedL.collect { case l: Call[_] => (l.f.namef, l.f) }
    /** second  gathering of SysInstr which can access  the layer's name, because  setName has been called   */
    val instrs = main :: getSysInstr(dag.visitedL)
    val t2: TabSymb[InfoType[_]] = mutable.HashMap.empty
    // we will  store information about parameters, such as the number of bits. Therefore, we  store them in the symbol table.
    t2 ++= f.p.toList.map(a => ("p" + a.name, InfoType(a, ParamD())))
    new DataProg[T, InfoType[_]](new DagInstr(instrs, dag), funs.map {
      case (k, v) ⇒ k -> DataProg(v)
    }, t2, f.p.toList.map("p" + _.name), List())
  }
}

/**
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
   *
   */
  def treeIfy(): DataProg[T, InfoType[_]] = {
    val p = this.asInstanceOf[DataProg[T, InfoType[_]]]
    val dagis2 = dagis.affectIfy(p.dagis.inputTwice) //also replaces access to data parameters by read
    //Affectation generated correspond precisely to nonGenerators.
    p.updateTsymb(dagis.newAffect.map(_.exp), Field())
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
    p.updateTsymb(dagis.newAffect.map(_.exp), Field())
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
    p.updateTsymb(dagis.newAffect.map(_.exp), Field())
    /** We generate also variable which are effective data parameters for called macro
     * their kind is set to StoredField() */
    val effectiveDataParam: HashSet[AST[_]] = HashSet() ++ dagis1.allGenerators.flatMap(
      { case CallProc(p, names, exps) => exps; case _ => List() })
    val dagis2 = dagis1.affectIfy(effectiveDataParam(_))
    /** effective result parameters which were already variables need to be re-registered as storedFields */
    val newStoredFiedl: List[AST[_]] = effectiveDataParam.toList.filter((a: AST[_]) => AST.isNotRead(a) || p.tSymbVar(a.name).k == Field())
    p.updateTsymb(newStoredFiedl, StoredField())
    val nbitExp: AstField[Int] = mutable.HashMap.empty
    val newFuns: TabSymb[DataProg[_, InfoNbit[_]]] = mutable.HashMap.empty
    /** stores the number of bits of parameters which are assumed to be ASTLs */
    val newtSymb: TabSymb[InfoNbit[_]] = mutable.HashMap.empty

    newtSymb ++= (paramD zip nbitP).map {
      case (nom, nbi) => nom -> new InfoNbit(tSymbVar(nom).t, tSymbVar(nom).k, nbi)
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
   *         and therefore directly executable as a loop on CA   */
  private def isLeafCaLoop: Boolean = funs.isEmpty && !tSymbVar.valuesIterator.exists(_.k.isStoredField)

  def macroIfy(): DataProg[T, InfoNbit[_]] = {
    def needStored(s: String): Boolean = tSymbVar(s).k.needStored

    /**
     * Creates a subFunction from a set of Affectation supposed to be in topological order (not completely sure, though)
     * DR parameter are repeated, but will be removed from results, when compiling the call, and the header.
     *
     * @param finstrs a set of affectation forming a connected component.
     */
    def builtFun(finstrs: Iterable[Affect[_]]): DataProg[_, InfoNbit[_]] = {
      val fparamR = finstrs.filter(a => needStored(a.name)).toList
      val fparamRname = fparamR.map(_.name)
      val fparamDfirst = toSet(finstrs.map(_.asInstanceOf[Affect[_]].exp.symbols.filter(needStored)).toList.flatten).toList
      /** Variables that are computed within new function should not be passed as data but as DR      */
      val fparamD = fparamDfirst.filter(!fparamRname.contains(_))
      val newtSymbVar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
      val t = tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]]
      for (p <- fparamD) {
        val old = t(p); newtSymbVar += p -> new InfoNbit(old.t, ParamD(), old.nb)
      }
      for (p <- finstrs) {
        val n = p.name; val old = t(n)
        newtSymbVar += n -> new InfoNbit(old.t, if (!needStored(p.name)) Field() else if (fparamD.contains(n)) ParamDR() else ParamR(), old.nb)
      }
      setInputNeighbor(finstrs.toList.asInstanceOf[List[Instr]]) // when using a data parameter in paramD, we should not include the instructions which were computing those parameter
      val newDagis = new DagInstr(fparamR) //instructions computing results are the roots.
      new DataProg(newDagis, mutable.HashMap.empty, newtSymbVar, fparamD, fparamRname)
    }

    /**
     * @param finstrs instructions forming a connected component
     * @return true if the instructions use only  concat or elt,
     *         it is not necessary to create a function, in this case.
     */
    def NeedBuiltFun(finstrs: Iterable[Instr]): Boolean = {
      for (i <- finstrs) if (!i.asInstanceOf[Affect[_]].exp.asInstanceOf[ASTL.ASTLg].justConcats) return true;
      false
    }

    val p = this.asInstanceOf[DataProg[T, InfoNbit[_]]]
    if (isLeafCaLoop) return p
    val proximity2: (Instr, Instr) => Boolean = {
      case (Affect(_, _), Affect(name, _)) => !needStored(name);

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
      newFuns.addOne(name -> builtFun(g.asInstanceOf[Iterable[Affect[_]]]))
      List(Instr(name, newFuns(name))) //computes a CallProc to the new function
    }

    val newDagis: Dag[Instr] = dagis.quotient2(proximity2, transform)
    new DataProg(newDagis, newFuns ++ funs.map { case (k, v) ⇒ k -> v.macroIfy() }, p.tSymbVar, paramD, paramR)
  }

  /**
   *
   * @return computes the offsets of the layers    */

  def foldRegister(offset: Integer): DataProg[_, InfoNbit[_]] = {


    val funs2 = funs.map { case (k, v) ⇒ k -> v.foldRegister() }
    val p = this.asInstanceOf[DataProg[T, InfoNbit[_]]]
    if (!isLeafCaLoop) return new DataProg(dagis, funs2, p.tSymbVar, paramD, paramR)
    /** Each instruction affecting  name, has a set of constraint indexed with name. */
    val constraints: TabSymb[Constraint] = mutable.HashMap.empty
    //dagis.visitedL=dagis.visitedL.map( (i:Instr)=>if(i.isTransfer) i.asInstanceOf[Affect[_]].align2(constraints) else i )
    dagis.visitedL = dagis.visitedL.map((i: Instr) => if (i.isTransfer) i.asInstanceOf[Affect[_]].align3(constraints) else i)

    val rewrite: Instr => Instr = (i: Instr) => if (i.isTransfer) i.asInstanceOf[Affect[_]].align3(constraints) else i
    val dagis2: DagInstr = dagis.propagateUnit(rewrite)

    for (i <- dagis2.visitedL) {
      i.reset
    } //simplicial instructions need not align
    if (!constraints.isEmpty) println("Constraint: " + constraints)

    // val notFolded  = mutable.HashSet.empty[String] //we must remember variables that could not be folded.
    val proximity2: (Instr, Instr) => Boolean = (x: Instr, y: Instr) => x.isTransfer == y.isTransfer

    def transform(g: Iterable[Instr]): List[Zone2] = List(Zone2(constraints, g.asInstanceOf[Iterable[Affect[_]]]))

    val zoneDag: Dag[Zone2] = dagis2.quotient2(proximity2, transform)
    zoneDag.visitedL.map(_.setPartitionOut()) //set partition constraints towards output neighbors

    zoneDag.visitedL.map(_.setFoldConstrSimplicial())

    zoneDag.visitedL.reverse.map(_.pick())
    print(zoneDag)


    /*    val (tInstrs, sInstrs) = instrs.partition(_.isTransfer) //transfer-instrs build TCCs, and then simplicial-instrs build SCCs
        val cc = components(instrs, (x: Instr, y: Instr) =>    x.isTransfer == y .isTransfer ) //zones are  connected subgraph of transfer or simplicial
        var zones: TabSymb[ZoneV ] = mutable.HashMap.empty
        val allZones=cc.map(ZoneV(_,zones, constraints ));
        zones++=   allZones.map((z:ZoneV)=>(z.name->z))
        val edges=allZones.flatMap( _.inNeighbors).toList
        for(z<-allZones) z.outNeighbors= edges.filter(_.in.name==z.name)
        //println(allZones.mkString("\n")+"\n")
        allZones.map(_.setFoldConstrSimplicial())
        // root instructions are those computing usefuell stuff.
        val minimalRootInstr   = tSymbVar.keys.filter(tSymbVar(_).k.needCompute) .map(definedBy(_).root)
        val minimalZones = rootInstrs(definedBy).map((i:Instr)=>a(i.root).name).map(zones).toList
        println("outputInstrs:" + minimalRootInstr.map((i:Instr)=>a(i.root).name))
        val z=dataStruc.Graph[ZoneV,EdgeZ](minimalZones)
        for(n<-z.nodes)     n.pick()
        println("Picked "+ z.nodes.mkString("\n")  )
        //val simplicialOutput = outn.filter(!_.isTransfer) */


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