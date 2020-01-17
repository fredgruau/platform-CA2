package compiler

import compiler.Constraint._
import compiler.Dag._
import compiler.ProgData._
import compiler.VarKind._

import scala.collection._
import scala.collection.mutable.LinkedHashMap

class ProgData2(val instrs: List[Instr], val funs: iTabSymb[ProgData2], val tSymbVar: TabSymb[InfoNbit[_]],
                val paramD: List[String], val paramR: List[String], val muInstrs: iTabSymb[List[Affect[_]]] = immutable.HashMap.empty //, val nbitExp: AstField[Int]
                ) {
  /** place anonymous macros first. */

  override def toString: String = (if (isMacro) "Macro:" else "Loop: ") + paramD.mkString(" ") + "=>" + paramR.mkString(" ") + "\n" +
    (if (muInstrs.isEmpty) instrs.mkString("") else instrs.map(v => "\n" + v + muInstrs(v.names(0)).mkString(" ")).mkString(" ")) + //print instr before muInstr decomposition.
    string(tSymbVar, "  |  ") + "\n" + listOf(funs).mkString("\n \n  ")

  def needStored(s: String): Boolean = tSymbVar(s).k.needStored
  def needStored(i: Instr): Boolean = needStored(i.names.head)

  def NeedBuiltFun(finstrs: Iterable[Instr]): Boolean = {
    for (i <- finstrs) if (!(i.asInstanceOf[Affect[_]].exp.concatElt)) return true
    return false
  }

  /**
   * Creates a subFunction from a set of Affectation supposed to be in topological order (not completely sure, though)
   * DR parameter are repeated, but will be removed from results, when compiling the call, and the header.
   * @Iterable[Instr] a set of affectation forming a connected component.
   */
  def builtFun(finstrs: Iterable[Instr]) = {
    val fparamD = (immutable.HashSet.empty[String] ++ finstrs.map(_.asInstanceOf[Affect[_]].exp.symbols.filter(needStored(_))).toList.flatten).toList
    val fparamR = finstrs.filter(needStored(_)).toList
    val newtSymbVar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    for (p <- fparamD) { val old = tSymbVar(p); newtSymbVar += p -> new InfoNbit(old.t, ParamD(), old.nb) }
    for (p <- finstrs) {
      val n = p.names(0); val old = tSymbVar(n);
      newtSymbVar += n -> new InfoNbit(old.t, if (!needStored(p)) Field() else if (fparamD.contains(n)) ParamDR() else ParamR(), old.nb)
    }
    new ProgData2(finstrs.toList, mutable.HashMap.empty, newtSymbVar, fparamD.toList, fparamR.map(_.names(0)))
  }

  /**Compute the Dag of instructions, where a neighbor is an input neigbor, i.e. affectation which set variables which are used, needs to compute definedBy*/
  def readDependancy(instrs: List[Instr], t: TabSymb[InfoNbit[_]]): iTabSymb[Instr] = {
    val definedBy: iTabSymb[Instr] = immutable.HashMap.empty ++ instrs.map(a => (a.names.map(_ -> a))).flatten
    for (a <- instrs) a.neighbor = List.empty[Instr] ++ a.usedVars.filter(v => definedBy.contains(v) && !t(v).k.isLayer).map(definedBy(_));
    definedBy
  }
  /**Obsolete, We now use a simpler way, visting from min element, where min is determined by varKind  */
  def writeDependency(instrs: List[Instr], t: TabSymb[InfoNbit[_]]) = {
    val usedBy: TabSymb[mutable.HashSet[Instr]] = mutable.HashMap.empty
    for (i <- instrs) for (v <- i.usedVars) {
      if (!usedBy.contains(v)) usedBy += v -> mutable.HashSet.empty[Instr]
      usedBy(v) += i
    }
    for (a <- instrs) a.neighbor = a.neighbor ++ a.names.filter(t(_).k.isLayer).map(s => (usedBy(s) - a).toList).flatten
    //if a layer is updated using its previous value it will create a loop on the updating instruction a.neighbor contains a, that's why we have to remove a explicitely
  }

  /**
   * we are carefull about the fact that the new value memorized in a layer is stored, after all the instructions reading the layer are done.
   * if the next value is to be reused, then, we must check that it is affected in another variable (because there will be two users: the memorize instr, and the other.
   */
  def isMacro = funs.isEmpty && tSymbVar.valuesIterator.find(_.k.notInMacro) == None
  def macroise(): ProgData2 = {
    if (isMacro) return this
    /** one reason why we do not replace param and layer construct by read, is to be able to remove them when they are useless (in non-macro direct affectation)*/
    val (affect2s, callprocs) = instrs.partition(_.isInstanceOf[Affect[_]])
    val affects = affect2s.filter(!_.useless) //selects Affects, au passage, removes those useless instr
    readDependancy(affects, tSymbVar)
    val cc = components(affects, (_: Instr, y: Instr) => !needStored(y))
    val (cc1, cc2) = cc.partition(NeedBuiltFun(_)) //cc2 uses only concat and elt, doesn't need a macro
    val builtFuns = immutable.HashMap.empty ++ cc1.map(setInstr => newFunName() -> builtFun(setInstr))
    val newInstrs = builtFuns.map { case (k, v) ⇒ Instr(k, v) }.toList ::: cc2.toList.flatten ::: callprocs
    val defby = readDependancy(newInstrs, tSymbVar);
    val root = tSymbVar.keys.filter(tSymbVar(_).k.isMin) //.partition(tSymbVar(_).k.isLayer )
    val (sorted, _) = getGreater((root.toList).map(defby(_)));
    new ProgData2(sorted.reverse, builtFuns ++ funs.map { case (k, v) ⇒ k → v.macroise() }, tSymbVar, paramD, paramR);
  }
  /**The symbol table is not expanded while variables are, therefore, to find out the type and number of bits of each variables, one must remove the suffixes. */
  def unfoldSpace(m: Machine): ProgData2 = {
    val funs2 = funs.map { case (k, v) ⇒ k → v.unfoldSpace(m) }
    if (isMacro) new ProgData2(instrs, funs2, tSymbVar, paramD, paramR, immutable.HashMap.empty ++ instrs.map(a => (a.names(0) -> a.unfoldSpace(m, tSymbVar).asInstanceOf[List[Affect[_]]])))
    else new ProgData2(instrs.map(_.unfoldSpace(m, tSymbVar)).flatten, funs2, tSymbVar, paramD, paramR)
  }

  /** returns an iterable of iterable of Instr, */
  def Tcomponent(l: List[Instr],   cs: TabSymb[immutable.HashSet[Constraint]] )=null
   
  /**the union is done with either all the outputneighbor or none, therefore before doing the union,
   *  we must test if all output neighbors are OK, this involves intersecting constraints and check there is a solution.
   *  The problem is, we need to compute a temporary union, each time we find a new component, 
   *  The solution is to gather all the constraint on the node being
   *  added, when we do the union   */
  def componentsSyncOutput[T <: Dag[T] with Union[T]](all: List[T], p: (T, T) => Boolean,considered: T => Boolean): Iterable[Iterable[T]] = {
    var  ok:Boolean=true
    for (src <- all) for (target <- src.neighbor) if(considered(target)) ok=ok &&  p(src, target) 
    if(ok) for (src <- all) for (target <- src.neighbor) if(considered(target)) if (p(src, target)) src.union(target);
    val m = LinkedHashMap.empty ++ all.map(x => (x -> x.root)); // print(m)
    m.groupBy(_._2).map { case (k, v) => v.keys }  
  }
  
  
  /**tries to reuse registers so as to have one or two registers for each instruction */
  def foldRegister(): ProgData2 = {
    val funs2 = funs.map { case (k, v) ⇒ k → v.foldRegister() }
    if (!isMacro) return this
    /**Each instruction affecting  name, has a set of constraint indexed with name. */
    val constraints: TabSymb[immutable.HashSet[Constraint]] = mutable.HashMap.empty
    /** We build  zone, associated to roots as we compute components, so as to be able later to propage constraints during the building itself,  if need be  */
    val zone: TabSymb[Zone[_]] = mutable.HashMap.empty
      readDependancy(instrs, tSymbVar)
    //we conpute simplicial and transfer connected components, Scc and Tcc
  //  val Scc = components(instrs, (x: Instr, y: Instr) => !x.asInstanceOf[Affect[_]].exp.asInstanceOf[ASTLg].locus.isTransfer)
    for (i <- instrs) i.align(constraints) 
  //i.alignPerm not being empty, the commming call to "components" will compute closure of alignement
  //  val Tcc = components(instrs, (x: Instr, y: Instr) => x.asInstanceOf[Affect[_]].exp.asInstanceOf[ASTLg].locus.isTransfer)

 //  println("totototot" + constraints)
    val definedBy: iTabSymb[Instr] = immutable.HashMap.empty ++ instrs.map(a => (a.names.map(_ -> a))).flatten
    //for cycle constraints, we look for delayed variables in order to   add a matching beginWith constraint.
    for (v <- constraints.keys) if(!constraints(v).filter(_.isInstanceOf[Cycle]).isEmpty){
      val xors = muInstrs(v) //we look which component can be delayed.
      var i = -1;  val delayedVar = xors.map(a => { i = i + 1; if (a.exp.firstArgDelayed(muInstrs)) Some(i) else None }).flatten
   //   we add a constraint to start by evaluating clock on a  delayedVar)
      if (!delayedVar.isEmpty)   constraints += v -> (constraints(v) + BeginWithEither(delayedVar))
    
    }
    if(!constraints.isEmpty) print("Constraint: "+constraints)
    null;
  }
}