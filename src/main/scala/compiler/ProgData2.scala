package compiler

import compiler.Constraint._
import compiler.Dag._
import compiler.ProgData._
import compiler.VarKind._
import scala.collection.{mutable, _}
import Align._
import Instr._

//noinspection FilterEmptyCheck,FilterEmptyCheck,EmptyCheck,ScalaUnnecessaryParentheses,ScalaUnnecessaryParentheses

/**
 * Contains all the data of a program
 *
 * @param instrs   spatial instructions
 * @param funs     macro or loops
 * @param tSymbVar info about variables: kind, number of birts,
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
    string(tSymbVar, "  |  ") + "\n" + listOf(funs).mkString("\n \n  ")


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

  /** instructions using variables **/

  private def outputNeighbor(i: Instr, u: Map[String, List[Instr]]) = u.getOrElse(a(i).name, List())

  /** Compute the Dag of instructions, where a neighbor is an input neigbor, i.e. affectation which set variables which are used, needs to compute definedBy
   * input neighbors are instructions which defines used Variables */
  private def readDependancy(instrs: List[Instr], t: TabSymb[InfoNbit[_]]): iTabSymb[Instr] = {
    val definedBy: iTabSymb[Instr] = immutable.HashMap.empty ++ instrs.flatMap(a => a.names.map(_ -> a))
    for (a <- instrs) a.inputNeighbors = List.empty[Instr] ++ a.usedVars.filter(v => definedBy.contains(v) && !t(v).k.isLayer).map(definedBy(_))
    definedBy
  }

  /*Obsolete, We now use a simpler way, visting from min element, where min is determined by varKind
  def writeDependency(instrs throw new RuntimeException("cycle detected in AST:" + path): List[Instr], t: TabSymb[InfoNbit[_]]): Unit = {
    val usedBy: TabSymb[mutable.HashSet[Instr]] = mutable.HashMap.empty
    for (i <- instrs) for (v <- i.usedVars) {
      if (!usedBy.contains(v)) usedBy += v -> mutable.HashSet.empty[Instr]
      usedBy(v) += i
    }
    for (a <- instrs) a.neighbor = a.neighbor ++ a.names.filter(t(_).k.isLayer).flatMap(s => (usedBy(s) -a ).toList)
    //if a layer is updated using its previous value it will create a loop on the updating instruction a.neighbor contains a, that's why we have to remove a explicitely
  }*/

  /**
   * we are carefull about the fact that the new value memorized in a layer is stored, after all the instructions reading the layer are done.
   * if the next value is to be reused, then, we must check that it is affected in another variable (because there will be two users: the memorize instr, and the other.
   */
  //noinspection EmptyCheck
  private def isMacro: Boolean = funs.isEmpty && !tSymbVar.valuesIterator.exists(_.k.notInMacro)

  def macroise(): ProgData2 = {
    if (isMacro) return this
    /** one reason why we do not replace param and layer construct by read, is to be able to remove them when they are useless (in non-macro direct affectation) */
    val (affect2s, callprocs) = instrs.partition(_.isInstanceOf[Affect[_]])
    val affects = affect2s.filter(!_.useless) //selects Affects, au passage, removes those useless instr
    readDependancy(affects, tSymbVar)
    val cc = components(affects, (_: Instr, y: Instr) => !needStored(y))
    val (cc1, cc2) = cc.partition(NeedBuiltFun) //cc2 uses only concat and elt, doesn't need a macro
    val builtFuns = immutable.HashMap.empty ++ cc1.map(setInstr => newFunName() -> builtFun(setInstr)) //defined macro, they contain only affectations.
    val newInstrs = builtFuns.map { case (k, v) ⇒ Instr(k, v) }.toList ::: cc2.toList.flatten ::: callprocs //replaced macroised sequence by calls
    val defby = readDependancy(newInstrs, tSymbVar)
    val root = tSymbVar.keys.filter(tSymbVar(_).k.isMin) //.partition(tSymbVar(_).k.isLayer )
    val (sorted, _) = getGreater(root.toList.map(defby(_)))
    new ProgData2(sorted.reverse, builtFuns ++ funs.map { case (k, v) ⇒ k -> v.macroise() }, tSymbVar, paramD, paramR)
  }

  /** The symbol table is not expanded while variables are, therefore, to find out the type and number of bits of each variables, one must remove the suffixes. */
  //noinspection ScalaUnnecessaryParentheses
  def unfoldSpace(m: Machine): ProgData2 = {
    val funs2 = funs.map { case (k, v) => k -> v.unfoldSpace(m) }
    if (isMacro) new ProgData2(instrs, funs2, tSymbVar, paramD, paramR, immutable.HashMap.empty ++ instrs.map(a => a.names.head -> a.unfoldSpace(m, tSymbVar).asInstanceOf[List[Affect[_]]]))
    else new ProgData2(instrs.flatMap(_.unfoldSpace(m, tSymbVar)), funs2, tSymbVar, paramD, paramR)
  }



  /** tries to reuse registers so as to have one or two registers for each instruction */
  //noinspection EmptyCheck,EmptyCheck,EmptyCheck
  def foldRegister(): ProgData2 = {
    val funs2 = funs.map { case (k, v) ⇒ k -> v.foldRegister() }
    if (!isMacro) return new ProgData2(instrs, funs2, tSymbVar, paramD, paramR)
    /** Each instruction affecting  name, has a set of constraint indexed with name. */
    val constraints: TabSymb[Constraint] = mutable.HashMap.empty
    val rootConstraintsT: TabSymb[Constraint] = mutable.HashMap.empty
    val rootConstraintsS: TabSymb[Constraint] = mutable.HashMap.empty //instruction with a reduce have both a constraintsT and a constraintsS!
    readDependancy(instrs, tSymbVar)
    for (i <- instrs) { i.align(constraints);   i.reset   }
    if (!constraints.isEmpty) println("Constraint: " + constraints)
    print(toStringHead + instrs.mkString(""))
    val notFolded  = mutable.HashSet.empty[String] //we must remember variables that cound not be folded.
    val (tInstrs, sInstrs) = instrs.partition(_.isTransfer) //transfer-instrs build TCCs, and then simplicial-instrs build SCCs
    TCCs(constraints, rootConstraintsT, tInstrs, notFolded)
    SCCs(constraints, rootConstraintsS, rootConstraintsT, sInstrs, notFolded)
    //print for verifying right behavior of TCC and SCC
    printConstraints(tInstrs, "transfer", rootConstraintsT, notFolded)
    printConstraints(sInstrs, "simplicial", rootConstraintsS, notFolded, rootConstraintsT)
    new ProgData2(instrs, funs2, tSymbVar, paramD, paramR, muInstrs)
  }

  private def printConstraints(l: List[Instr], typeZone: String, rootConstraints: TabSymb[Constraint], notFolded: mutable.HashSet[String],rootConstraints2: TabSymb[Constraint]=null): Unit = {
    val cc = paquets(l);  var n = 0
    for (instrs2 <- cc) //we print the constraint for each components, they are associated to the root of the component.
      if (notFolded.contains(a(instrs2.head).name)) println(a(instrs2.head).name + " is not Folded")
      else { n = n + 1;val name=a(instrs2.head.root).name
        println("      paquet de " + instrs2.size + " instruction, de racine: ", instrs2.head.root, " de schedule "
          + rootConstraints(name) )
        if(rootConstraints2!=null && rootConstraints2.contains(name))   println("the schedule for inner reduction is " + rootConstraints2 (name))
      }
    println("==> In total, there is: " + n + " " + typeZone + " zone synchronized")
  }

  /** When encountering a cycle constr, we tries to spare register further */
  private def addConstr(constraints: TabSymb[Constraint], s: String, c: Constraint) = {
    if (constraints.contains(s))
      constraints.addOne(s -> constraints(s).intersect(c))
    else constraints.addOne(s -> c)
  }

  /** Computes output neighours */
  private lazy val usedBy: iTabSymb[List[Instr]] = {
    var r: iTabSymb2[List[Instr]] = immutable.HashMap.empty; for (i <- instrs) for (v <- i.usedVars) r = r + (v -> (i :: r.getOrElse(v, List()))); r
  }

  /** Only to be called if current function is a macro.
   * Set the root field, neighorfield, alignperm field of  instructions affecting a transfer field
   * so as to define Synchronized TCCs
   * @param constraints     input constraints of variable set by affect instructions.
   * @param rootConstraints output constraints defined for roots, aligned to root of computed TCCs.
   * @param transferInstr transfer instructions that are analysed
   * @param notFolded : register variable names that could not be folded.
   **/
  private def TCCs(constraints: TabSymb[Constraint], rootConstraints: TabSymb[Constraint], transferInstr: List[Instr], notFolded: mutable.HashSet[String]): Unit = {
    for (iTransfer <- transferInstr.reverse)
      {  val nameTransfer=a(iTransfer).name
        var constraintCur: Constraint =   constraints.getOrElse(nameTransfer,AllConstr(6)) //we start with all schedules, unless we found a cycle constraint    during the calls to align
         val n = outputNeighbor(iTransfer, usedBy).filter(_.isTransfer) //we consider only transfer output neighbor, candicate to be unioned to form a bigger TCCs.
        val cc = paquets(n);  for (instrs2 <- cc) //instruction in instr2   share same root
          if (!constraintCur.empty) {
            val aligns = immutable.HashSet.empty[Array[Int]] ++ instrs2.map((i2: Instr) =>
              compose(invert(i2.alignPerm(nameTransfer)), i2.alignToRoot))
            val align = aligns.size match { //how to align i to instr2's root.
              case 2 => //if there is two alignement, we can get away by add a cycle constraint.
                val List(sched1, sched2) = aligns.toList
                val constr = Cycle(compose(invert(sched1), sched2))
                constraintCur = constraintCur.intersect(constr)
              //  addConstr(constraints, nameTransfer, constr) //we loose the information on the cycle nature of the constraints?.
                sched2
              case 1 => aligns.head //there is only one alignement nothing to do.
              case _ => throw new RuntimeException(" regarde ce bordel de plus prés!" + aligns)
            }
            val nameN = a(instrs2.head.root).name //root variable of TCC instr2 , TODO we should index constraint on components, not on instruction's root
            if (rootConstraints.contains(nameN)) //if the cc is not singleton, its rootconstraint has been computed for root
              constraintCur = constraintCur.intersect(rootConstraints(nameN).permute(invert(align))) // we consider it
          }
        if (constraintCur.empty) notFolded.add(nameTransfer)
        else { //constraints can be applied, so we can proceed to make the union of itransfer with all output TCCs
           for (instrs2 <- cc) iTransfer.union(instrs2.head) //builds larger TCC
          rootConstraints.addOne(a(iTransfer.root).name -> constraintCur.permute(iTransfer.alignToRoot)) //every non singleton TCC's component will have a constraint on its root.
        }
      }
  }

  private def polishConstraint(cs: TabConstr): Unit = {
    for (v <- cs.keys) if (cs(v).isInstanceOf[Cycle]) {
      val xors = muInstrs(v) //we look which component can be delayed.
      var i = -1
      val delayedVar = xors.flatMap(a => {
        i = i + 1
        if (a.exp.firstArgDelayed(muInstrs)) Some(i) else None
      })
      //   we add a constraint to start by evaluating clock on a  delayedVar)
      if (delayedVar.nonEmpty) addConstr(cs, v, BeginWithEither(delayedVar, 6))

    }
  }

  /** Computes simpilicial components.
   * @param rootConstraintsT output constraints on possible schedules, defined for roots of Transfer components.
   * @param rootConstraintsS output constraints on possible schedules, defined for roots of Simplicial components.
   * @param simplicialInstr  : instruction affecting a variable of simplicial type, V,E or F
   * @param notFolded : register variable names that could not be folded.
   **/
  private def SCCs(constraints: TabSymb[Constraint], rootConstraintsS: TabSymb[Constraint], rootConstraintsT: TabSymb[Constraint], simplicialInstr: List[Instr], notFolded: mutable.HashSet[String]): Unit = {
    for (iSimplic <- simplicialInstr.reverse) {
      val nameSimplic: String = a(iSimplic).name
      val locusSimplic = a(iSimplic).exp.asInstanceOf[ASTLt[_, _]].locus.asInstanceOf[S]
      var constraintCur: Constraint = AllConstr(locusSimplic.arity) //we start with all possible schedules, and add constraints as we meet them
      //step 1, we consider output instruction of simplicial type
      val outn = outputNeighbor(iSimplic, usedBy)
      val simplicialOutput = outn.filter(!_.isTransfer) //// we do the union of the constraints of simplicial output neighbors
      for (instrs2 <- paquets(simplicialOutput)) { //instruction of instr2 have been visited already, they share same root
        if (constraints.contains(nameSimplic)) //useless for the moment since align only generate constraints for transfer instructions.
          constraintCur = constraintCur.intersect(constraints(nameSimplic)) //we instersect with the found constraint
        val rootName = a(instrs2.head.root).name //root variable of SCC ,
        if (rootConstraintsS.contains(rootName)) //if it has a constraint
          constraintCur = constraintCur.intersect(rootConstraintsS(rootName)) //we do not need to align
      }
      //step 2, we add the projection of constraint of output transfer instructions
      /** we need a place to store temporary new root constraints, until we knwow that the union can indeed be done */
      val newRootConstrT :TabSymb[Constraint]= mutable.HashMap.empty  //used to update the transfer constraints, by adding partition.
      val transferOutput = outn.filter(_.isTransfer)
      for (instrs2 <- paquets(transferOutput)) { //we consider components
        val iRepr = instrs2.head
        val rootName = a(iRepr.root).name //root variable of TCC ,
        val constrPartition: Constraint = Partition.partOrAll(iRepr.alignPerm(nameSimplic), locusSimplic)
        var constrPartPerm = constrPartition.permute(iRepr.alignToRoot)
        if (rootConstraintsT.contains(rootName)) //add a constraint from the root if there is one
          constrPartPerm = constrPartPerm.intersect(rootConstraintsT(rootName))
        addConstr(newRootConstrT ,rootName , constrPartPerm)
        val p = constrPartPerm.permute(invert(iRepr.alignToRoot)).project(locusSimplic.arity)
        constraintCur = constraintCur.intersect(p)
      }
      //step 3, we add the projection of contraint of input transfer instructions
      val transferInput = iSimplic.inputNeighbors.filter(_.isTransfer)
      for (instrs2 <- paquets(transferInput)) {
        val iRepr = instrs2.head
        val rootName = a(iRepr.root).name //root variable of TCC ,
        val constrPartition: Constraint = Partition.partOrAll(locusSimplic)
        var constrPartPerm = constrPartition.permute(iRepr.alignToRoot)
        if (rootConstraintsT.contains(rootName)) //add a constraint from the root if there is one
          constrPartPerm = constrPartPerm.intersect(rootConstraintsT(rootName))
        addConstr(newRootConstrT,rootName, constrPartPerm)
        val p = constrPartPerm.permute(invert(iRepr.alignToRoot))
        addConstr(newRootConstrT ,nameSimplic , p) //iSimplic is a reduce (Only a single reduce generates simplicial from transfer), hence we would also need a transfer schedule for this reduce
        val pp = p.project(locusSimplic.arity)
        constraintCur = constraintCur.intersect(pp)
      }
      //if the total resulting constraint  "contraintCur" is not satisfiable, iSimpoic is declared not foldable, else we proceed to build a new component
      if (constraintCur.empty) notFolded.add(nameSimplic) //constraints can be apply, so we can proceed to make the union of i with all output TCCs
      else {
        for (instrs2 <- paquets(simplicialOutput)) iSimplic.union(instrs2.head, doAlign = false) // there is no need to compute alignement to root for simplicial instr, since it always the neutral element.
        rootConstraintsS.addOne(nameSimplic -> constraintCur.permute(iSimplic.alignToRoot))
        rootConstraintsT.addAll(newRootConstrT)
      }
    }
  }
}

