package compiler

import compiler.Constraint._
import dataStruc.DagNode._
import compiler.ProgData._
import compiler.VarKind._
import compiler.Circuit._
import scala.collection.{mutable, _}
import dataStruc.Align._
import Instr._
import dataStruc.Graph.getSmaller

//noinspection FilterEmptyCheck,FilterEmptyCheck,EmptyCheck,ScalaUnnecessaryParentheses,ScalaUnnecessaryParentheses

/**
 * Contains all the data of a program
 *
 * @param instrs   spatial instructions
 * @param funs     macro or loops
 * @param tSymbVar info about variables: kind, number of bits,
 * @param paramD   data input
 * @param paramR   result output.
 * @param muInstrs for each spatial variables,   list   affectations of its scalar components. (6 for Transfer type)
 */
class ProgData2(private val instrs: List[Instr],private  val funs: iTabSymb[ProgData2], val tSymbVar: TabSymb[InfoNbit[_]],
                val paramD: List[String], val paramR: List[String], val muInstrs: iTabSymb[List[Affect[_]]] = immutable.HashMap.empty //, val nbitExp: AstField[Int]
               ) {
  /** place anonymous macros first. */
  private def toStringHead: String = (if (isMacro) "Macro:" else "Loop: ") + paramD.mkString(" ") + "=>" + paramR.mkString(" ") + "\n"
  override def toString: String = toStringHead + (if (muInstrs.isEmpty) instrs.mkString("") else instrs.map(v => "\n" + v + muInstrs(v.names.head).mkString(" ")).mkString(" ")) +
    DataProg.string(tSymbVar, "  |  ") + "\n" + listOf(funs).mkString("\n \n  ")


  //private def usedBy: iTabSymb[List[Instr]] = {var r:iTabSymb[List[Instr]]=Map.empty;  for(i<- instrs) for(v<-i.usedVars) r=r+ (v-> (i::r.getOrElse(v,List()))) ; return (r)}
  private def needStored(s: String): Boolean = tSymbVar(s).k.needStored
  private def needStored(i: Instr): Boolean = needStored(i.names.head)
  private def NeedBuiltFun(finstrs: Iterable[Instr]): Boolean = {
    for (i <- finstrs) if (!i.asInstanceOf[Affect[_]].exp.concatElt) return true
    false
  }

  /**
   * Creates a subFunction from a set of Affectation supposed to be in topological order (not completely sure, though)
   * DR parameter are repeated, but will be removed from results, when compiling the call, and the header.
   * @param finstrs a set of affectation forming a connected component.
   */
  private def builtFun(finstrs: Iterable[Instr]): ProgData2 = {
    val fparamD = (immutable.HashSet.empty[String] ++ finstrs.map(_.asInstanceOf[Affect[_]].exp.symbols.filter(needStored)).toList.flatten).toList
    val fparamR = finstrs.filter(needStored).toList
    val newtSymbVar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    for (p <- fparamD) {
      val old = tSymbVar(p); newtSymbVar += p -> new InfoNbit(old.t, ParamD(), old.nb)
    }
    for (p <- finstrs) {
      val n = p.names.head; val old = tSymbVar(n)
      newtSymbVar += n -> new InfoNbit(old.t, if (!needStored(p)) Field() else if (fparamD.contains(n)) ParamDR() else ParamR(), old.nb)
    }
    new ProgData2(finstrs.toList, mutable.HashMap.empty, newtSymbVar, fparamD, fparamR.map(_.names.head))
  }
  /**
   * we are carefull about the fact that the new value memorized in a layer is stored, after all the instructions reading the layer are done.
   * if the next value is to be reused, then, we must check that it is affected in another variable (because there will be two users: the memorize instr, and the other.
   */
  //noinspection EmptyCheck
  private def isMacro: Boolean = funs.isEmpty && !tSymbVar.valuesIterator.exists(_.k.notInMacro)

  /**
   * @return Instructions that computes variable directly needed.
   */
  private def rootInstrs(d:iTabSymb[Instr])= tSymbVar.keys.filter(tSymbVar(_).k.needCompute) .map(d(_))
  def macroise(): ProgData2 = {
    if (isMacro) return this
    /** one reason why we do not replace param and layer construct by read, is to be able to remove them when they are useless (in non-macro direct affectation) */
    val (affect2s, callprocs) = instrs.partition(_.isInstanceOf[Affect[_]])
    val affects = affect2s.filter(!_.useless) //selects Affects, au passage, removes those useless instr
    setInputNeighbor(affects, tSymbVar, definedBy)
    val cc = components(affects, (_: Instr, y: Instr) => !needStored(y))
    val (cc1, cc2) = cc.partition(NeedBuiltFun) //cc2 which uses only concat and elt, doesn't need a macro
    val builtFuns = immutable.HashMap.empty ++ cc1.map(setInstr => newFunName() -> builtFun(setInstr)) //defined macro, they contain only affectations.
    val newInstrs = builtFuns.map { case (k, v) ⇒ Instr(k, v) }.toList ::: cc2.toList.flatten ::: callprocs //replaced macroised sequence by calls
    val d = defby(newInstrs)
    setInputNeighbor(newInstrs, tSymbVar, d)
    val (sorted, _) = getGreater(rootInstrs(d).toList)
    new ProgData2(sorted.reverse, builtFuns ++ funs.map { case (k, v) ⇒ k -> v.macroise() }, tSymbVar, paramD, paramR)
  }

  /** The symbol table is not expanded while variables are, therefore,
   * to find out the type and number of bits of each variables, one must remove the suffixes. */
  //noinspection ScalaUnnecessaryParentheses
  def unfoldSpace(m: Machine): ProgData2 = {
    val funs2 = funs.map { case (k, v) => k -> v.unfoldSpace(m) }
    if (isMacro) new ProgData2(instrs, funs2, tSymbVar, paramD, paramR, immutable.HashMap.empty ++ instrs.map(a => a.names.head -> a.unfoldSpace(m, tSymbVar).asInstanceOf[List[Affect[_]]]))
    else new ProgData2(instrs.flatMap(_.unfoldSpace(m, tSymbVar)), funs2, tSymbVar, paramD, paramR)
  }

  private def printConstraints(l: List[Instr], typeZone: String, rootConstraints: TabSymb[Constraint], notFolded: mutable.HashSet[String], rootConstraints2: TabSymb[Constraint] = null): Unit = {
    val cc = paquets(l).filter(_.head.locus.get != V());
    var n = 0
    for (instrs2 <- cc) { //we print the constraint for each components, they are associated to the root of the component.
      print("      paquet de " + instrs2.size + " instructions\n" //, de racine: ", instrs2.head.root
       + instrs2.mkString(";"))

      if (notFolded.contains(a(instrs2.head).name)) println( a(instrs2.head).name + " This " + typeZone +  " zone cannot fold")
      else { n = n + 1;val name=a(instrs2.head.root).name
        print( " de schedule "     + rootConstraints.getOrElse(name,"->pas de schedule! ") + " sur "+name )
        println( " de locus " + instrs2.head.root.locus.get )
        if(rootConstraints2!=null && rootConstraints2.contains(name))   println("the schedule for inner reduction is " + rootConstraints2 (name))
      }}
    if(cc.size>0)    println("==> In total, there is: " + n + " " + typeZone + " zone synchronized\n")
  }
  /** When encountering a cycle constr, we tries to spare register further */
  private def addConstr(constraints: TabSymb[Constraint], s: String, c: Constraint) = {
    if (constraints.contains(s))
      constraints.addOne(s -> constraints(s).intersect(c))
    else constraints.addOne(s -> c)
  }

  /** Computes output neighours */
  private lazy val usedBy: iTabSymb[List[Instr]] = {
    var r: iTabSymb2[List[Instr]] = immutable.HashMap.empty;
    for (i <- instrs) for (v <- i.usedVars) r = r + (v -> (i :: r.getOrElse(v, List())));
    r
  }

  /** wrapper consulting used by to retrieve instructions comming after i, using variable created by i **/
  private def outputNeighbor(i: Instr): List[Instr] = usedBy.getOrElse(a(i).name, List())

  /** Computes a map variable name -> instruction defining that variable */
  private lazy val definedBy: iTabSymb[Instr] = defby(instrs)

  private def defby(i: List[Instr]): iTabSymb[Instr] = immutable.HashMap.empty ++ i.flatMap(a => a.names.map(_ -> a))

  /** Compute the Dag of instructions, where a neighbor is an input neigbor,
   * i.e. affectation which set variables which are used,
   * input neighbors are instructions which defines used Variables */
  private def setInputNeighbor(instrs: List[Instr], t: TabSymb[InfoNbit[_]], d: iTabSymb[Instr]) = {
    for (a <- instrs) a.inputNeighbors = List.empty[Instr] ++ a.usedVars.filter(v => d.contains(v) && !t(v).k.isLayer).map(d(_))
  }

  /** Add constraints for sparing register for multicasts */
  private def polishConstraint(cs: TabConstr, defby: iTabSymb[Instr]): Unit = {
    for (v <- cs.keys) if (cs(v).isInstanceOf[Cycle]) {
      val xors = muInstrs(v) //we look which component can be delayed.
      var i = -1
      val delayedVar = xors.flatMap(a => {
        i = i + 1
        if (a.exp.firstArgDelayed(muInstrs)) Some(i) else None
      })
      //   we add a constraint to start by evaluating clock on a  delayedVar)
      if (delayedVar.nonEmpty) addConstr(cs, v, BeginWithEither(delayedVar, defby(v).locus.get))
    }
  }
  /**
   * @return a graph of zones with constraints, and foldability.
   */
  def foldRegister():ProgData2= {
    val funs2 = funs.map { case (k, v) ⇒ k -> v.foldRegister() }
    if (!isMacro) return new ProgData2(instrs, funs2, tSymbVar, paramD, paramR)
    /** Each instruction affecting  name, has a set of constraint indexed with name. */
    val constraints: TabSymb[Constraint] = mutable.HashMap.empty
    setInputNeighbor(instrs, tSymbVar, definedBy)
    for (i <- instrs) {
      if (i.isTransfer) i.align(constraints); i.reset
    } //simplicial instructions need not align
    if (!constraints.isEmpty) println("Constraint: " + constraints)
    val notFolded = mutable.HashSet.empty[String] //we must remember variables that cound not be folded.
    val (tInstrs, sInstrs) = instrs.partition(_.isTransfer) //transfer-instrs build TCCs, and then simplicial-instrs build SCCs
    val cc = components(instrs, //zones are  connected subgraph of transfer or simplicial
      (x: Instr, y: Instr) => x.isTransfer == y.isTransfer)
    var zones: TabSymb[ZoneV] = mutable.HashMap.empty
    val allZones = cc.map(ZoneV(_, zones, constraints));
    zones ++= allZones.map((z: ZoneV) => (z.name -> z))
    val edges = allZones.flatMap(_.inNeighbors).toList
    for (z <- allZones) z.outNeighbors = edges.filter(_.in.name == z.name) //set output neighbors in a second step
    //println(allZones.mkString("\n")+"\n")
    allZones.map(_.setFoldConstrSimplicial())
    // root instructions are those computing usefull stuff.
    val minimalRootInstr = tSymbVar.keys.filter(tSymbVar(_).k.needCompute).map(definedBy(_).root)
    val minimalZones = rootInstrs(definedBy).map((i: Instr) => a(i.root).name).map(zones).toList
    // println("outputInstrs:" + minimalRootInstr.map((i:Instr)=>a(i.root).name))
    val z = dataStruc.Graph[ZoneV, EdgeZ](minimalZones)
    // for(n<-z.nodes)     n.pick() ;
    println("Picked " + z.nodes.mkString("\n"))
    //val simplicialOutput = outn.filter(!_.isTransfer)
    new ProgData2(instrs, funs2, tSymbVar, paramD, paramR, muInstrs)
  }

}

