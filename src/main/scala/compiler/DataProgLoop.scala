
package compiler

import compiler.AST.isNotRead
import compiler.ASTB.{AffBool, Dir, Elt, Reduce, outputStored}
import compiler.ASTBfun.ASTBg
import compiler.Circuit.{TabSymb, iTabSymb}
import dataStruc.{DagInstr, WiredInOut}

import scala.collection.{Set, immutable, mutable}
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
  def totalCode(): List[ASTBt[B]] = loops.flatMap(_.loops.flatMap(_.boolAST))

  /**
   * now displaying instructions involves goign through the associated loops of loops
   **/
  override def toStringInstr = "there is " + dagis.visitedL.length + " instructions\n" +
    (if (loops == null) dagis.visitedL.reverse.map((i: Instr) => i.toString() + "\n").mkString("")
    else loops.mkString("\n"))

  /**
   * mapping of tmpVar to registers.
   */
  def coalescTMP = if (loops != null) loops.map(_.coalescTmp).reduce(((x, y) => x ++ y)) else null

  /**
   *
   * @return we need to add the coalescing of temporary variables.
   */
  override def toString = super.toString + "\n" + toStringCoalesc(coalescTMP)

  /**
   *
   * @return generates a list of list of boolean code for each instruction
   */
  def unfoldInt(): DataProgLoop[U] = {

    /** values of constant registers,  so that it can be propagated */

    if (isLeafCaLoop) {
      loops.map(_.unfoldInt())
      new DataProgLoop[U](dagis, funs.map { case (k, v) ⇒ k -> v.unfoldInt }, tSymbVar, paramD,
        paramR, coalesc, loops)
    }
    else
      new DataProgLoop[U](dagis, funs.map { case (k, v) ⇒ k -> v.unfoldInt }, tSymbVar, paramD,
        paramR, coalesc, loops)
  }
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

  /**
   *
   * @return hashmap describing how to best map tmp register to local registers, so as to minimize their number
   */
  def coalescTmp: iTabSymb[String] = {
    WiredInOut.heap(loops).map((x: (String, Int)) => (x._1 -> ("r" + x._2)))
  }

  /**
   *
   * @return side effect, adds the boolean code to each packet of loops
   */
  def unfoldInt(): Unit = {
    loops.map(_.addUnfoldInt())


    // val coalesced = codeNloop.map(_.map(_.coalesc(coalescTable)))

  }
}






