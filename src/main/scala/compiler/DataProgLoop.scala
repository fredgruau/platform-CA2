
package compiler

import compiler.AST.isNotRead
import compiler.ASTB.{AffBool, Dir, Elt, Reduce, outputStored}
import compiler.ASTBfun.ASTBg
import compiler.Circuit.{TabSymb, iTabSymb}
import compiler.Instr.{a, deployInt}
import compiler.VarKind.{MacroField, StoredField}
import dataStruc.{DagInstr, DagNode, HeapStates, WiredInOut}
import scala.collection.{Map, Set, immutable, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.mutable.ArrayBuffer

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
 * @param coalesc  identical coalesced form for identifiers which are regrouped in class.
 * @param loops    regroup the boolean code into packets executable as loops, in order to allow pipelining
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
   * entire binary code before coalesc
   */
  def totalCode = if (loops != null) loops.flatMap(_.loops.flatMap(_.boboolAST)) else null

  /** name of scan variables, that should enter the symbol table. */
  var scNames: List[String] = null

  /**
   * now displaying instructions involves goign through the associated loops of loops
   **/
  override def toStringInstr = "there is " + (if (loops == null) dagis.visitedL.length else loops.length) + " instructions\n" +
    (if (loops == null) dagis.visitedL.reverse.map((i: Instr) => i.toString() + "\n").mkString("")
    else loops.mkString("\n")) //+  (if(isRootMain) "\n\n"+codeGen().mkString("\n")   else "")


  /** compute the number of gates needed to execute the function */
  def totalOp: Int =
    if (loops != null)
      loops.flatMap(_.loops.map(_.totalOp)).reduce(_ + _)
    else
      funs.values.map(_.asInstanceOf[DataProgLoop[_]].totalOp).reduce(_ + _)


  override def toStringHeader: String = {
    super.toStringHeader +
      (if (loops != null) {
        val code: List[ASTBt[B]] = totalCode

        /** @param s name of a variable
         * @return true if that variable is a macroField
         */
        def isMacro(s: String): Boolean = {
          //removes the hashtag
          val s2 = if (s.contains('#')) s.substring(0, s.indexOf('#')) else s
          tSymbVarSafe(s2).k == MacroField()
        }

        val totalNames: Set[String] = ASTB.names(code).filter(isMacro(_))
        " register memory=" + totalNames.size + " bits, complexity=" + totalOp + "  operators "
      }
      else if (isRootMain) {
        def isHeap(s: String) = s.startsWith("Mem[")

        val totalNamesSubMain: Set[String] = dagis.visitedL.flatMap(_.names).filter(isHeap(_)).toSet
        val totalNamesRootMain: Set[String] = coalesc.values.filter(isHeap(_)).toSet
        val heapSize = totalNamesSubMain.union(totalNamesRootMain).size
        "CA memory size=" + heapSize + " "
      } else "")


  }


  /**
   * gather from every instructions, the mapping of temporary variables to registers.
   */
  def coalescTMP =
    if (loops != null)
      loops.map(_.coalescTmp).reduce(((x, y) => x ++ y)) else null

  /**
   *
   * @return we need to add the coalescing of temporary variables.
   */
  override def toString =
    super.toString + "\n" + "tmp registers:" + toStringCoalesc(coalescTMP) +
      (if (loops != null) "\n" + totalCode.map(_.toStringTree).mkString("  ") else "") + "\n" +
      toStringFuns

  /**
   *
   * @return generates a list of list of boolean affectations for each instruction
   */
  def unfoldInt(): DataProgLoop[U] = {
    val newParamD = paramD.flatMap((name: String) => deployInt(name, tSymbVarSafe(name).nb)) //generates boolean parameter from int parameters
    val newParamR = paramR.flatMap((name: String) => deployInt(name, tSymbVarSafe(name).nb)) //generates boolean parameter from int parameters
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


  /*
    def oldcoaalesc(): DataProgLoop[U] = {
      /**
       *
       * @param coal coalesc x-> y between int
       * @return extend t so as to coalesc between bool x#0->y#0, x#1->y#1, x#2->y#2
       *         the resulting array will be the new coalesc array
       */
      def extendToBool(coal: iTabSymb[String]) = {
        var result: iTabSymb[String] = HashMap()
        for (k <- coal.keys)
          if (tSymbVarSafe(k).nb > 1)
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
      if (isLeafCaLoop) {
        //updates the symbol table
        allCoalesc = extendToBool(coalesc) ++ coalesc ++ coalescTMP //we keep coalesc so that invariant remains correct
        val maxTmpReg: Int = loops.map(_.nbTmpReg).reduce(Math.max) //max number of register used.
        for (i <- 0 to maxTmpReg - 1) //adds in the symbol table, the register used for coalescing temp variables
          tSymbVar.addOne("r" + i -> new InfoNbit(B(), MacroField(), 1).asInstanceOf[U])
        loops.map(_.coalesc(allCoalesc)) //applies the  coalesc extended to bool, for all the code
      }
      else {
        // for main loop allcoalesc will contain heap adress of variables, global adress of layers,
        // including bug field and  pix fields,
        // we create fake instructions, in order to forget layers in usedVar and names, and then be able to
        // reuse the heap fonctionality of WiredInOut.
        val noLayersInstr = dagis.visitedL.reverse.map((i: Instr) => new InstrNoLayersNorParam(i, tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]]))
        val adressOfStoredLayer: Map[String, Int] = WiredInOut.heap(noLayersInstr) // defines adress for intermediate stored Fields
        val layers: List[String] = tSymbVar.toList.filter(_._1.startsWith("ll")).filter(_._2.nb == 1).map(_._1).sorted
        val nbLayers = layers.length
        allCoalesc = HashMap()
        if (isRootMain)
          allCoalesc ++= //we therefore store all the adresses, layers and heap, as strings so as to store them in allcoalesc
            (layers zip (0 to nbLayers - 1)).map((e: (String, Int)) => (e._1, e._2.toString)) ++ //adress of layers
              (paramR zip (nbLayers to nbLayers + paramR.length)).map((e: (String, Int)) => (e._1, e._2.toString)) //adresses of (unique) return parameter
        val occupied = allCoalesc.size
        allCoalesc ++= adressOfStoredLayer.toList.map((e: (String, Int)) => (e._1, (e._2 + occupied).toString)) //adress of stored Fields
      }
      new DataProgLoop[U](dagis, funs.map { case (k, v) ⇒ k -> v.coaalesc() }, tSymbVar, paramD,
        paramR, allCoalesc, loops)
    }
    */
  /** size of CA memory in bits, exept for the memory needed to store the display which can be very big */
  var heapSize = 0

  /**
   * allocate both CA lines for main loop, and Registers, for CA loops.
   *
   * @return coalesced form of the program, where both the number of CA lines, and registers used is minimized.
   *         using a simple and classic heap
   */
  def coaalesc(): DataProgLoop[U] = {
    /**
     *
     * @param coal coalesc x-> y between int
     * @return extend t so as to coalesc between bool x#0->y#0, x#1->y#1, x#2->y#2
     *         the resulting array will be the new coalesc array
     */
    def extendToBool(coal: iTabSymb[String]) = {
      var result: iTabSymb[String] = HashMap()
      for (k <- coal.keys)
        if (tSymbVarSafe(k).nb > 1)
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
    var newDagis: DagInstr = dagis
    if (isLeafCaLoop) {
      //updates the symbol table
      allCoalesc = extendToBool(coalesc) ++ coalesc ++ coalescTMP //we keep coalesc so that invariant remains correct
      val maxTmpReg: Int = loops.map(_.nbTmpReg).reduce(Math.max) //max number of register used.
      for (i <- 0 to maxTmpReg - 1) //adds in the symbol table, the register used for coalescing temp variables
        tSymbVar.addOne("r" + i -> new InfoNbit(B(), MacroField(), 1).asInstanceOf[U])
      loops.map(_.coalesc(allCoalesc)) //applies the  coalesc extended to bool, for all the code
    }
    else if (isRootMain) { //we generate a list of call proc only for the main root
      val (callProcs, allAdresses) = codeGen()
      newDagis = DagInstr(callProcs)
      //in order to compute the code of a callProc,
      //we will prefer to leave the name of variables in the mainRoot it is more clear,
      //we compute coalesc, but we do not replace in expressions, the variable name x by Mem[11] for example
      //instead we will simply compile x=Mem[11] before.
      allCoalesc = HashMap() ++
        allAdresses.toList.map((e: (String, Int)) => (e._1, "Mem[" + (e._2).toString + "]".toString)) //      It can be used to coalesc
    }
    new DataProgLoop[U](newDagis, funs.map { case (k, v) ⇒ k -> v.coaalesc() }, tSymbVar, paramD,
      paramR, allCoalesc, loops)
  }

  /** list of calls produce by mainRoot together with adresses of variables in the heap */
  def codeGen(): (List[CallProc], iTabSymb[Int]) = {
    var res: List[CallProc] = List()
    val noLayersInstr = dagis.visitedL.reverse.map((i: Instr) => new InstrNoLayersNorParam(i, tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]]))
    //by building instr which ignore layers we prevent allocation of layers in the heap. layers are allocated as global variables.
    var allAdresses: iTabSymb[Int] = HashMap()
    val emptyCoalesc: iTabSymb[String] = HashMap()
    val layers: List[String] = tSymbVar.toList.filter(_._1.startsWith("ll")).filter(_._2.nb == 1).map(_._1).sorted
    val nbLayers = layers.length
    allAdresses ++= //we store all the adresses, layers and heap, as strings so as to store them in allcoalesc
      (layers zip (0 to nbLayers - 1)) //adress of layers
    (paramR zip (nbLayers to nbLayers + paramR.length)) //adresses of  result parameter to the mainRoot
    val nbGlobals = allAdresses.size //the number of variables allways in the heap,
    // where morover, the distincts bit planes are found in sequence in the heap
    val hs = new HeapStates[InstrNoLayersNorParam](noLayersInstr)
    for ((instr, (heapCur, adresses)) <- dagis.visitedL.reverse zip hs) {
      res = res ++ instr.codeGen(heapCur, funs, nbGlobals, emptyCoalesc)
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
   * @param params   parameters.
   * @return
   */
  def codeGen(h: Vector[String], nbGlobal: Int, params: iTabSymb[String]): List[CallProc] = {
    var res: List[CallProc] = List()
    val noLayersInstr = dagis.visitedL.reverse.map((i: Instr) => new InstrNoLayersNorParam(i, tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]]))
    var allCoalesc = params //initial values of coalesc are just param, then we'll add the MEME
    if (!isLeafCaLoop) {
      assert(!isRootMain) //we must be in main non root, because codeGen of main root does not take adresses
      //val hs=new HeapStates[Instr](dagis.visitedL.reverse, h)  //todo enlever les parametres de names et de used.
      val hs = new HeapStates[InstrNoLayersNorParam](noLayersInstr, h) //dagis.visitedL.reverse)
      for ((instr, (heapCur, adresses)) <- dagis.visitedL.reverse zip hs) {
        allCoalesc = allCoalesc ++ adresses.toList.map((e: (String, Int)) => (e._1, "Mem[" + (e._2 + nbGlobal).toString + "]"))
        res = res ++ instr.codeGen(heapCur, funs, nbGlobal, allCoalesc) //we directly update the coalesc table adding the new adress to the parameters
        // instr.codeGen call recursively this.codeGen
      }
      heapSize = Math.max(heapSize, hs.heapSize) //codegen of a proc may be called several times with different heap size.
      //right nowe we recompute heapSize, instead of storing it.
      res
    }
    else
      throw new Exception("we compile main")
  }
}


/** wrapper to instructions that redefines usedVar and names by supressing layers, so that we can use the heap fonctionality */
class InstrNoLayersNorParam(val instr: Instr, val t: TabSymb[InfoNbit[_]]) extends DagNode[InstrNoLayersNorParam] with WiredInOut[InstrNoLayersNorParam] {

  /** Layers and param, do not need to be stored in the heap, they ve got a fixed place */
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
  for (p <- loops.reverse) tmpLiveIntVars = p.tmpLiveBefore(tmpLiveIntVars) //compute the tmpVariables live after the loops
  /**
   *
   * @return instead of a flat list of instruction we use a more structured display
   *         for each instructions, we indicate how many loops are needed, then we list those loops, and
   *         for each loop, we show the direction, bit size, then the pipelined affect, the affect, and the binary code
   */
  override def toString = "INSTR " + instrNumber + " ON " + loops.size + " LOOPS     " + affect +
    /*     coalescTmp +*/ "\n" +
    loops.mkString("\n") + "\n"

  /** number of temporary registers needed to implement the instructions, initialized when we instanciate the registers */
  var nbTmpReg: Int = -1

  /**
   *
   * @return hashmap describing how to best map tmp register to local registers, so as to minimize their number
   */
  def coalescTmp: iTabSymb[String] = {
    val res = WiredInOut.heap(loops).map((x: (String, Int)) => (x._1 -> ("r" + x._2)))
    nbTmpReg = res.values.toSet.size //pretty heavy computation but does the job
    res
  }

  /**
   *
   * @return side effect, adds the boolean code to each packet of loops
   */
  def unfoldInt(): Unit = loops.map(_.addUnfoldInt())

  /**
   *
   * @return side effect, minimize the number of used register
   */
  def coalesc(c: iTabSymb[String]): Unit = loops.map(_.addCoalesc(c))

}




