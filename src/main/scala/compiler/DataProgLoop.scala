
package compiler

import compiler.AST.{Read, isNotRead}
import compiler.ASTB.{AffBool, Dir, Elt, False, Reduce, outputStored}
import compiler.ASTBfun.ASTBg
import compiler.SpatialType.BoolV
import compiler.Circuit.{TabSymb, iTabSymb}
import dataStruc.Util.{radicalOfVar, removeAfterChar, shortenedSig}
import compiler.Instr.{a, deployInt2}
import compiler.Locus.{all2DLocus, allLocus}
import compiler.VarKind.{MacroField, StoredField}
import dataStruc.{DagInstr, DagNode, HeapStates, Named, WiredInOut}

import scala.::
import scala.collection.IterableOnce.iterableOnceExtensionMethods
import scala.collection.immutable.Nil.:::
import scala.collection.{Map, Set, immutable, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.mutable.ArrayBuffer
import scala.io.Source

/** wrapper to instructions that redefines usedVar and names by supressing layers, so that we can use the heap fonctionality */
class InstrNoLayersNorParam(val instr: Instr, val t: TabSymb[InfoNbit[_]]) extends DagNode[InstrNoLayersNorParam] with WiredInOut[InstrNoLayersNorParam] {

  /** Layers and param, do not need to be stored in the heap, they ve got a fixed place
   * data Parameters to show, they also do need to be stored */
  def needAdressInHeap(s: String): Boolean = {
    !s.startsWith("ll") && (t(s).k == StoredField())
  }

  /** names of variables read by instruction. */
  override def usedVars(): Predef.Set[String] = instr.usedVars().filter(needAdressInHeap(_))

  /** names of variables produced by instruction. */
  override def names: List[String] = instr.names.filter(needAdressInHeap(_))
}

/**
 * Contains the info necessary to compile one instructions
 *
 * @param affect the instruction which wil be compiled into a doubly nested loop of booleans
 * @param loops  the list of packets each executable using a single loop, in topological order??.
 */
class InstrLoop(val affect: Instr, val loops: List[Packet], val instrNumber: Int) {
  //set the live variables of each packet
  var tmpLiveIntVars: Predef.Set[String] = Predef.Set()
  for (p <- loops.reverse)
    tmpLiveIntVars = p.tmpLiveBefore(tmpLiveIntVars) //compute the tmpVariables live after the loops

  /**
   *
   * @return instead of a flat list of instruction we use a more structured display
   *         for each instructions, we indicate how many loops are needed, then we list those loops, and
   *         for each loop, we show the direction, bit size, then the pipelined affect, the affect, and the binary code
   */
  override def toString = {
    val c= loops.mkString("\n")
    "INSTR " + instrNumber + " ON " + loops.size + " LOOPS     " + affect +
      /*     coalescTmp +*/ "\n" + c+ "\n"
  }

  /** number of temporary registers needed to implement the instructions, initialized when we instanciate the registers */
  var nbTmpReg: Int = -1

  /** @return hashmap describing how to best map tmp register to local registers, so as to minimize their number */
  def coalescTmp: iTabSymb[String] = {
    val res: Map[String, String] = WiredInOut.heap(loops).map((x: (String, Int)) => (x._1 -> ("r" + x._2)))
    nbTmpReg = res.values.toSet.size //pretty heavy computation but does the job
    res
  }

  /** @return side effect, adds the boolean code to each packet of loops
   */
  def unfoldInt(): Unit = loops.map(_.addUnfoldInt())

  /**
   *
   * @return side effect, minimize the number of used register
   */
  def coalesc(c: iTabSymb[String]): Unit = loops.map(_.addCoalesc(c))

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
 * @param coalesc  identical coalesced form for identifiers which can be stored on a single int.
 * @param loops    this is what's new compared to dataProg. It regroups the boolean code into packets executable as loops, in order to allow pipelining
 */
class DataProgLoop[U <: InfoNbit[_]](override val dagis: DagInstr, override val funs: iTabSymb[DataProgLoop[U]],
                                     override val tSymbVar: TabSymb[U],
                                     override val paramD: List[String], override val paramR: List[String],
                                     override val coalesc: iTabSymb[String], val loops: List[InstrLoop])
  extends DataProg[U](dagis, funs, tSymbVar, paramD, paramR, coalesc) {
  /**
   *
   * @return the concatenation of all the binary code
   */

  /**
   * entire binary code of CAloop, coalesced
   */
  def totalCodeCoalesced: List[ASTBt[B]] =
    if (loops != null)
      loops.flatMap(_.loops.flatMap(_.boboolAST)) else null
  /**
   * entire binary code of CAloop, not coalesced
   */
  def totalCodeUnCoalesced: List[ASTBt[B]] =
    if (loops != null)
      loops.flatMap(_.loops.flatMap(_.boolAST)) else null

  /** name of scan variables, that should enter the symbol table. */
  var scNames: List[String] = null

  /**
   * now displaying instructions involves going through the associated loops of loops
   * */
  override def toStringInstr = "there is " + (if (loops == null) dagis.visitedL.length else loops.length) + " instructions\n" +
    (if (loops == null) dagis.visitedL.reverse.map((i: Instr) => i.toString() + "\n").mkString("")
    else loops.mkString("\n")) //+  (if(isRootMain) "\n\n"+codeGen().mkString("\n")   else "")


  lazy val  gateCountMacroLoop:Int={
    assert( loops!=null)//we must have a leaf CA
    loops.flatMap(_.loops.map(_.totalOp)).reduce(_ + _)
  }

  /** compute the number of gates needed to execute the function*/
  def totalOp: Int =
    if (loops != null) //we have a leaf CA
      loops.flatMap(_.loops.map(_.totalOp)).reduce(_ + _)
    else //we sum the gate count of leaf ca. TODO not sure about that, since a leafCA could be used more than once we should sum over how many calls
      if (funs.nonEmpty)
        funs.values.map(_.asInstanceOf[DataProgLoop[_]].totalOp).reduce(_ + _)
      else 0


  /** @param s name of a variable
   * @return true if that variable is a macroField
   */
  def isMacro(s: String): Boolean = tSymbVarSafe(removeAfterChar(s, '#')).k == MacroField()

  lazy val totalNames: Set[String] =
    ASTB.names(totalCodeCoalesced).filter(isMacro(_))

  private def registerCount: Int = {
    assert(loops != null)
    totalNames.size
  }

  /** @param s name of a variable
   * @return true if that variable is a bit plane number.
   */
  def isHeap(s: String): Boolean = s.startsWith("mem[")

  /** if variables s  is "mem[14]" returns 14 */
  def adress(s: String) = s.substring(4, s.length - 1).toInt

  lazy val totalNamesSubMain: Set[String] = dagis.visitedL.flatMap(_.names).filter(isHeap(_)).toSet //we look at the call
  lazy val totalNamesRootMain: Set[String] = coalesc.values.filter(isHeap(_)).toSet


  def mainHeapSize = totalNamesSubMain.union(totalNamesRootMain).size

  override def toStringHeader: String = {
    super.toStringHeader +
      (if (loops != null) " register memory=" + registerCount + " bits, complexity=" + totalOp + "  operators "
      else if (isRootMain) "CA memory size=" + mainHeapSize + " "
      else "")


  }


  /**
   * gather from every instructions, the mapping of temporary variables to registers.
   */
  lazy val coalescTMP =
    if (loops != null)
      loops.map(_.coalescTmp).reduce(((x, y) => x ++ y)) else null

  /**
   *
   * @return we need to add the coalescing of temporary variables.
   */
  override def toString = {
    val s=super.toString
    s
      // +(if(coalescTMP!= null&&coalescTMP.size>0) "tmp registers:" + toStringCoalesc(coalescTMP) else "" ) +
    /*  (if (loops != null) {
        val t=totalCodeUnCoalesced
        assert(t!=null)//detect too early call to totalCode
        "Total code of macro: " +
        //totalCode.map(_.toStringTreeInfix(tSymbVar.asInstanceOf[TabSymb[InfoType[_]]])).grouped(4).map(_.mkString(";")).mkString(";\n ") else "")
        t.map(_.toStringTreeInfix(this.asInstanceOf[DataProg[InfoType[_]]])).grouped(4).map(_.mkString(";")).mkString(";\n ")
      }
      else "")
*/
  }
  /**
   * @return generates a list of list of boolean affectations for each instruction
   */
  def unfoldInt(): DataProgLoop[U] = {
    val newParamD = paramD.flatMap((name: String) => deployInt2(name, tSymbVarSafe(name))) //generates boolean parameter from int parameters
    val newParamR = paramR.flatMap((name: String) => deployInt2(name, tSymbVarSafe(name))) //generates boolean parameter from int parameters
    if (isLeafCaLoop) {
      loops.map(_.unfoldInt())
      new DataProgLoop[U](dagis, funs, tSymbVar, newParamD, newParamR, coalesc, loops)
    }
    else {
      var newCoalesc: TabSymb[String] = mutable.HashMap() //stores coalesc from bool to int
      val rewriteBool: Instr => List[Instr] = (i: Instr) => i.unfoldInt(tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]])
      val newInstr = dagis.visitedL.flatMap(rewriteBool).reverse
      //val dagisBool=dagis.propagate(rewriteBool) //this would use the generators to regenerate the dag, but this is not correct because the generators have been lost
      val dagisBool = DagInstr(newInstr)
      new DataProgLoop[U](dagisBool, funs.map { case (k, v) ⇒ k -> v.unfoldInt }, tSymbVar, newParamD, newParamR, coalesc, loops)
    }

  }

  /** size of CA memory in bitplanes, exept for the memory needed to store the display which is alsoo quite big */
  var heapSize = 0

  /**
   * coalescing means that many variables (either CA lines or integer register in CA loops)
   * are assigned the same register
   * allocate both CA lines for main loop, and Registers, for CA loops.
   *
   * @return coalesced form of the program, coalescing of variables is done on index of memory bit planes.
   *         where both the number of CA bit planes, and registers used is minimized.
   *         using a simple and classic heap
   */
  def coaalesc(): DataProgLoop[U] = {
    /**
     * @param coal coalesc x-> y between int
     * @return extend t so as to coalesc between bool x#0->y#0, x#1->y#1, x#2->y#2
     *         the resulting array will be the new coalesc array
     */
    def extendToBool(coal: iTabSymb[String]) = {
      var result: iTabSymb[String] = HashMap()
      for (k <- coal.keys)
        //if (tSymbVarSafe(k).nb > 1)
          if (tSymbVarSafe(k).ring != B())  //on décide qu'on séme du #0 a tout vent
        //we need to check if k+"#"+i happens to also be coalesced to k, in which case we have a "chained coalesc"
          for (i <- 0 to tSymbVarSafe(k).nb - 1) {
            result = result + (k + "#" + i -> (coal(k) + "#" + i))
            //we add the boolean entry in tabsymb
            tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]].addOne(coal(k) + "#" + i -> new InfoNbit[B](B(), tSymbVar(coal(k)).k, 1))
          }
        else result = result + (k -> coal(k))
      result
    }

    /** stores registers for CAloops, and array plan for isMainRoot
     * The code of  non main root, is transfered to main loop */
    var allCoalesc: iTabSymb[String] = HashMap()
    var newDagis: DagInstr = dagis //we keep the same dagis for CAloop
    if (isLeafCaLoop) { // we generate a macro
      //updates the symbol table
      allCoalesc = extendToBool(coalesc) ++ coalesc ++ coalescTMP //we keep coalesc so that invariant remains correct
      val maxTmpReg: Int = loops.map(_.nbTmpReg).reduce(Math.max) //max number of register used.
      for (i <- 0 to maxTmpReg - 1) //adds in the symbol table, the register used for coalescing temp variables
        tSymbVar.addOne("r" + i -> new InfoNbit(B(), MacroField(), 1).asInstanceOf[U])
      loops.map(_.coalesc(allCoalesc)) //applies the  coalesc extended to bool, for all the code
    }
    else if (isRootMain) { //we generate a list of call proc only for the main root, the other prog are explored from the main loop.
      val (callProcs: List[CallProc], allAdresses: iTabSymb[Int]) = codeGenMain()
      newDagis = DagInstr(callProcs)
      //in order to compute the code of a callProc,
      //we will prefer to leave the name of variables in the mainRoot it is more clear,
      //we compute coalesc, but we do not replace in expressions, the variable name x by mem[11] for example
      //instead we will simply compile x=mem[11] before.
      allCoalesc = HashMap() ++
        allAdresses.toList.map((e: (String, Int)) => (e._1, "mem[" + (e._2).toString + "]".toString)) //      It can be used to coalesc
    }

    val fun2=funs
    new DataProgLoop[U](newDagis, funs.map { case (k, v) ⇒ k -> v.coaalesc() }, tSymbVar, paramD,
      paramR, allCoalesc, loops) with ProduceJava[U]
  }


  /**
   * to be executed only by the main dataProg
   *
   * @return list of calls produce by mainRoot together with adresses of variables in the heap
   *
   */
  def codeGenMain(): (List[CallProc], iTabSymb[Int]) = {
    var res: List[CallProc] = List()
    val noLayersInstr = dagis.visitedL.reverse.map((i: Instr) => new InstrNoLayersNorParam(i, tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]]))
    //by building instr which ignore layers we prevent allocation of layers in the heap. layers are allocated as global variables.
    var allAdresses: iTabSymb[Int] = HashMap() //will allocate one memory slot for each scalar variables
    val emptyCoalesc: iTabSymb[String] = HashMap()
    for (s <- layerSubProg2.keys)
      tSymbVar.addOne((s, layerSubProg2(s))) //adds to tSymbVar, constant layers defined in subProgram in tSymbVar
    val layerSpace: Int = layerSubProg2.map(l => l._2.asInstanceOf[InfoNbit[_]].density).sum
    //we store all the adresses, layers and heap, as strings so as to store them in allcoalesc
    allAdresses ++= (layerSubProg2.toList.flatMap(l => l._2.locus.deploy2(l._1, l._2.asInstanceOf[InfoNbit[_]])) zip (0 to layerSpace - 1)) //adress of layers
    allAdresses ++= (paramR zip (layerSpace to layerSpace + paramR.length)) //adresses of  result parameter to the mainRoot
    val nbGlobals = allAdresses.size //the number of variables allways in the heap,
    // where morover, the distincts bit planes are found in sequence in the heap
    val shown = dagis.visitedL.flatMap({ case i: CallProc =>
      if (i.procName.eq("show")) i.exps.map(_.asInstanceOf[Read[_]].which) else List()
    case _ => List()
    })
    val isshownAndNotGlobal = mutable.LinkedHashSet[String]() ++ shown diff allAdresses.keys.toSet //some shown variable are already in the globals, we do not need to show them
    val hs = new HeapStates[InstrNoLayersNorParam](noLayersInstr, Vector(null), isshownAndNotGlobal)
    //On itere sur hs. cela est complexe, on recupere pour chaque instr, l'état courant du heap pour modeliser un appel a une autre CAbranche      res = res ++ instr.codeGen(heapCur, funs, nbGlobals, emptyCoalesc)
    for ((instr, (heapCur, adresses: iTabSymb[Int])) <- dagis.visitedL.reverse zip hs) {
      res = res ++ instr.codeGenInstr(heapCur, funs, nbGlobals, emptyCoalesc)
      allAdresses ++= adresses.toList.map((e: (String, Int)) => (e._1, nbGlobals + (e._2)))
    }
    heapSize = hs.heapSize + nbGlobals
    (res, allAdresses)
  }

  /**
   * list of calls produce by non mainRoot
   *
   * @param h        initial occupancy of heap
   * @param nbGlobal number of global varialbes
   * @param params   correspondance from formal parameters to effective parameters.
   * @return calls compiled from non mainRoot
   */
  def codeGen(h: Vector[String], nbGlobal: Int, params: iTabSymb[String]): List[CallProc] = {
    var res: List[CallProc] = List()
    val noLayersInstr = dagis.visitedL.reverse.map((i: Instr) => new InstrNoLayersNorParam(i, tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]]))
    var allCoalesc: iTabSymb[String] = params //initial values of coalesc are just param, then we'll add the MEME
    if (!isLeafCaLoop) {
      assert(!isRootMain) //we must be in main non root, because codeGen of main root does not take adresses
      //val hs=new HeapStates[Instr](dagis.visitedL.reverse, h)  //todo enlever les parametres de names et de used.
      val hs = new HeapStates[InstrNoLayersNorParam](noLayersInstr, h) //dagis.visitedL.reverse)
      for ((instr, (heapCur, adresses)) <- dagis.visitedL.reverse zip hs) {
        allCoalesc = allCoalesc ++ adresses.toList.map((e: (String, Int)) => (e._1, "mem[" + (e._2 + nbGlobal).toString + "]"))
        res = res ++ instr.codeGenInstr(heapCur, funs, nbGlobal, allCoalesc) //we directly update the coalesc table adding the new adress to the parameters
        // instr.codeGen call recursively this.codeGen
      }
      heapSize = Math.max(heapSize, hs.heapSize) //codegen of a proc may be called several times with different heap size.
      //right nowe we recompute heapSize, instead of storing it.
      res
    }
    else
      throw new Exception("we compile main")
  }

  def isBoolV(str: String) = tSymbVarSafe(str).t == (V(), B()) // .isInstanceOf[BoolV]
  def needOnlyoneBit(str: String)= {
    val one=tSymbVarSafe(str).nb==1
    val l=tSymbVarSafe(str).locus
    val two = (l==V())
    one && two  }
  // def isIntV1(str: String) = tSymbVarSafe(str).t == (V(), Int(1)) // .isInstanceOf[BoolV]

  //

  /**
   * @return reconstruct all the macro loop, using a recursive call
   *  Data computed only once from the mainDataProgLoop, using def and lazy
   *  or.... may be also for intermediates fun which are not the main but which contain loop.
   *  carefull: it WILL NOT containt loop which where already compiled
   *
   */
  private def subDP: iTabSymb[DataProg[U]] = funs ++ funs.flatMap({ case (k, v) => v.subDP })

  /** hashmap of all the progCA except the main. It is undexed by their name,
   * it works only if called from the first global main loop */

  lazy val subDataProgs: iTabSymb[DataProgLoop[U]] = {
    val sub=subDP.asInstanceOf[iTabSymb[DataProgLoop[U]]] //used only for the main data Prog, this is why we put a lazy
    sub
  }

  /**
   *
   * @param progs map of programms, whose layers have been entered in tabSymb of the main entry point dataProg
   * @return all the layers.
   */
  def layers(progs: List[DataProgLoop[U]]): Map[String, U] =
    progs.flatMap(
    _.tSymbVar.filter(x =>
    {val isll=     Named.isLayer(x._1)  //name should start with "ll"
    val typeLayer= x._2.k.isLayerField  //we check the type for it can happen that paramR start with ll
     val nodol= Named.noDollarNorHashtag(x._1)
  isll&&typeLayer&&nodol}
  ).toList).toMap //if a $ or a # is present, it not a layer but only a layer component

  /** does not take into account the layers of this */
  lazy val layerSubProgStrict = layers(subDataProgs.values.toList) //: Predef.Map[String, U] = ( subDataProgs.values.toList).flatMap(_.tSymbVar.filter(x => x._2.k.isLayerField).toList).toMap
  /** takes into account the layer of this */
  lazy val layerSubProg2 = layers(this :: subDataProgs.values.toList) //(this :: subDataProgs.values.toList).flatMap(_.tSymbVar.filter(x =>  x._2.k.isLayerField).toList).toMap
  //lazy val layersMain: Predef.Map[String, U] =layers(List(this))
  /**
   *
   * @param nameFile non du fichier à trous
   * @param map      spécifie par quoi on remplace chaque trous, les quels sont occupés par les clefs de la map
   * @return resultat aprés remplacement.
   */
  def replaceAll(nameFile: String, map: iTabSymb[String]): String = {
    val template: String = Source.fromFile(nameFile).getLines().mkString("\n")
    val Regexp = """\{\{([^{}]+)\}\}""".r
    def replace(incoming: String) = {
      def replace(what: String, `with`: String)(where: String) = where.replace(what, `with`)
      val composedReplace = Regexp.findAllMatchIn(incoming).map { m => replace(m.matched, map(m.group(1)))(_) }.reduceLeftOption((lf, rf) => lf compose rf).getOrElse(identity[String](_))
      composedReplace(template)
    }
    replace(template)
  }


  /** outputs the sequence of all codes to macro loops */

  /** Asuming we kept original spatial variables in symbol table returns the list of spatial tpes, mixing data and result parameters */
  def spatialSig: List[(Locus, Ring)] = (shortenedSig(paramD) ::: shortenedSig(paramR)).map(tSymbVarSafe(_).t.asInstanceOf[(Locus, Ring)])

  /** Asuming we kept original spatial variables in symbol table returns the list of bit size, mixing data and result parameters */
  def nbitSig: List[Int] = (shortenedSig(paramD) ::: shortenedSig(paramR)).map(tSymbVarSafe(_).nb)

}

