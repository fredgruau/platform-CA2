
package compiler

import compiler.AST.isNotRead
import compiler.ASTB.{AffBool, Dir, Elt, Reduce, outputStored}
import compiler.ASTBfun.ASTBg
import compiler.ASTL.BoolV
import compiler.Circuit.{TabSymb, iTabSymb}
import compiler.DataProgLoop.{removeAfterChar, shortenedSig}
import compiler.Instr.{a, deployInt}
import compiler.VarKind.{MacroField, StoredField}
import dataStruc.{DagInstr, DagNode, HeapStates, WiredInOut}
import scala.collection.{Map, Set, immutable, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.mutable.ArrayBuffer
import scala.io.Source

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

  /** @return hashmap describing how to best map tmp register to local registers, so as to minimize their number */
  def coalescTmp: iTabSymb[String] = {
    val res = WiredInOut.heap(loops).map((x: (String, Int)) => (x._1 -> ("r" + x._2)))
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

object DataProgLoop {
  private def removeAfterChar(s: String, c: Char): String = if (s.contains(c)) s.substring(0, s.indexOf(c)) else s

  private def truncateBefore(s: String, p: String) = {
    if (s.indexOf(p) == -1) s else s.substring(0, s.indexOf(p))
  }

  private def radicalOfVar(s: String): String = {
    truncateBefore(truncateBefore(s, "$"), "#")
  }

  private def shortenedSig(param: List[String]): List[String] = {
    val res: mutable.LinkedHashSet[String] = mutable.LinkedHashSet()
    for (p <- param) res += radicalOfVar(p)
    return res.toList;
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
   * entire binary code of CAloop, before coalesc
   */
  lazy val totalCode: List[ASTBt[B]] = if (loops != null) loops.flatMap(_.loops.flatMap(_.boboolAST)) else null

  /** name of scan variables, that should enter the symbol table. */
  var scNames: List[String] = null

  /**
   * now displaying instructions involves going through the associated loops of loops
   * */
  override def toStringInstr = "there is " + (if (loops == null) dagis.visitedL.length else loops.length) + " instructions\n" +
    (if (loops == null) dagis.visitedL.reverse.map((i: Instr) => i.toString() + "\n").mkString("")
    else loops.mkString("\n")) //+  (if(isRootMain) "\n\n"+codeGen().mkString("\n")   else "")


  /** compute the number of gates needed to execute the function */
  def totalOp: Int =
    if (loops != null) //we have a leaf CA
      loops.flatMap(_.loops.map(_.totalOp)).reduce(_ + _)
    else //we sum the gate count of leaf ca. TODO not sure about that, since a leafCA could be used more than once we should sum over the called macro
      funs.values.map(_.asInstanceOf[DataProgLoop[_]].totalOp).reduce(_ + _)


  /** @param s name of a variable
   * @return true if that variable is a macroField
   */
  def isMacro(s: String): Boolean = tSymbVarSafe(removeAfterChar(s, '#')).k == MacroField()

  lazy val totalNames: Set[String] = ASTB.names(totalCode).filter(isMacro(_))

  private def registerCount: Int = {
    assert(loops != null)
    totalNames.size
  }

  /** @param s name of a variable
   * @return true if that variable is a bit plane number.
   */
  def isHeap(s: String): Boolean = s.startsWith("Mem[")

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
  override def toString =
    super.toString +
      // (if(coalescTMP!= null&&coalescTMP.size>0) "tmp registers:" + toStringCoalesc(coalescTMP) else "" ) +
      (if (loops != null) "Total code of macro: " + totalCode.map(_.toStringTreeInfix(tSymbVar.asInstanceOf[TabSymb[InfoType[_]]])).grouped(4).map(_.mkString(";")).mkString(";\n ") else "")

  /**
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

  /** size of CA memory in bitplanes, exept for the memory needed to store the display which is alsoo quite big */
  var heapSize = 0

  /**
   * coalescing means that many variables (either CA lines or integer register in CA loops)
   * are assigned the same register
   * allocate both CA lines for main loop, and Registers, for CA loops.
   *
   * @return coalesced form of the program, where both the number of CA bit planes, and registers used is minimized.
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
    var newDagis: DagInstr = dagis //we keep the same dagis for CAloop
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
      //iterer sur hs est complexe, on recupere pour chaque instr, l'état courant du heap pour modeliser un appel a une autre CAbranche      res = res ++ instr.codeGen(heapCur, funs, nbGlobals, emptyCoalesc)
      allAdresses ++= adresses.toList.map((e: (String, Int)) => (e._1, nbGlobals + (e._2)))
      val n = 0
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


  /**
   *
   * @return bitPlanes indexes associated to spatial variables
   */

  def isBoolV(str: String) = tSymbVarSafe(str).t == (V(), B()) // .isInstanceOf[BoolV]

  /** returns all the leafCAlloops, undexed by their name in an hashmap */
  def allCAloop: Iterable[(String, DataProgLoop[U])] = {
    def f(st: Tuple2[String, DataProgLoop[U]]) = if (st._2.isLeafCaLoop) List(st._1 -> st._2) else st._2.allCAloop

    funs.map(f(_)).flatten
  }

  def javaCode: String = javaCodeMain + allCAloop.map { case (k, v) => v.javaCodeCAloop(k) }.mkString("\n")

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

  def javaCodeMain: String =
    replaceAll("src/main/scala/compHandCA/templateCA.txt", Map(
      "NAMECA" -> paramR(0).capitalize,
      "MEMWIDTH" -> ("" + mainHeapSize)) //TODO on calcule pas bien la memwidth)
    )
  // shorten to " +    (shortenedSignature(paramD) ++ shortenedSignature(paramR)).mkString(" ") + "\n"


  def javaCodeCAloop(nameMacro: String): String = {
    val shortSigIn = shortenedSig(paramD);
    val shortSigOut = shortenedSig(paramR)

    /** add type to parameters, one dimension is enough for spatial type boolV, two dimensions are needed for other locus */
    def javaIntArray(s: String) = (if (isBoolV(s)) ("int [] ") else ("int [][] ")) + s

    val parameters = (shortSigIn ::: shortSigOut).map(javaIntArray(_))

    def anchorParam(shortened: List[String], original: List[String]): List[String] = {
      var res: List[String] = List()
      var i = 0
      for (s: String <- shortened) {
        if (isBoolV(s)) i += 1
        else {
          var j = 0
          try while (removeAfterChar(original(i), '$') == s) {
            res = original(i) + "=" + s + "[" + j + "]" :: res //ish=isE[0]
            j += 1;
            i += 1

          } catch {
            case _: IndexOutOfBoundsException =>
          }
        }
      }
      res
    }

    replaceAll("src/main/scala/compHandCA/templateCAloop.txt", Map(
      "NAMEMACRO" -> nameMacro,
      "PARAMETERS" -> parameters.mkString(","),
      "ANCHORPARAM" -> (anchorParam(shortSigIn, paramD) ::: anchorParam(shortSigOut, paramR)).reverse.mkString(","),
      "PROPAGATEFIRSTBIT" -> paramD.map((s: String) => "p.propagate4shift(" + s + ")").mkString(";"),
      "FIRSTPARAM" -> (paramD ::: paramR)(0), //There must be at least one param,
      // we need to read it so as to know the length which is the number of CA lines.
      //  "READPARAM"->paramD.map((s:String)=>s+"i"+"="+s+"[i]").mkString(";"),
      "DECLINITPARAM" -> {
        val intReg = (standaloneRegister ++ coalesced.keys)
        val boolReg: Iterable[String] = intReg.flatMap((s: String) => deployInt(s, tSymbVarSafe(s).nb))

        def isDelayed(s: String) = delayed.contains(removeAfterChar(s, '#'))

        "int " + boolReg.map((s: String) => if (isDelayed(s)) s + "=0" else s).mkString(",")
      },
      "LOOPBODY" -> totalCode.map(_.toStringTreeInfix(tSymbVar.asInstanceOf[TabSymb[InfoType[_]]])).grouped(4).map(_.mkString(";")).mkString(";\n ")

    ))
  }

}

