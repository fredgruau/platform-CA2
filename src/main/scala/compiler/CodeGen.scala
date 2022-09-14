/*
package compiler

import AST.{Call2, Param, Read, isNotRead}
import ASTB.{AffBool, Elt, ParOp, Reduce, Scan1, Scan2, outputStored, fromBoolB, nbitExpAndParam}
import ASTBfun.{ASTBg, minSI}
import Circuit.{TabSymb, iTabSymb}
import compiler.VarKind.MacroField
import dataStruc.DagInstr

import scala.collection.{immutable, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.mutable.ArrayBuffer

/**
 * contains all the information needed to produces ASTBt[B] code for one instruction
 * @param tSymbVar needed to know the bit size and wether a variable is "arithmetic" or not
 * @param coalesc  if string is not found in tSymbvar, try to find coalesc(String)
 *                 todo:  do not use this class to compute the number of bit in nbitR
 **/
class CodeGen(val tSymbVar: TabSymb[InfoNbit[_]], val coalesc: iTabSymb[String] = HashMap.empty) {
  /**
   *
   * @param x name of scalar variable
   * @param i loop index
   * @return  returns x plus i if non boolean,  so as to generate a different register for each loop index
   *          checking if boolean requires the use of many tables.
   *          checking if boolean requires the use of many tables.
   */
def addSufx(x: String, i: Int) = {
    val sufx = if (isBool(x)) ""
    else {
      if (i == -1) {
        val u = isBool(x)
        throw new Exception("indice -1")
      }

      "#" + i
    }
    x + sufx
  }

  /** evaluated(x)=i iff pipelined affectation x<-exp has been done for itération i. */
  var evaluated: iTabSymb[Int] = null
  var pipelined: Set[Instr] = HashSet()
  var tablePipelined: iTabSymb[Instr] = new immutable.HashMap()
  var tableAllPipelined: iTabSymb[Instr] = new immutable.HashMap()
  var pipelinedVariableUse: iTabSymb[Int] = null
  /** contains all the true affects adressable, as opposed to pipelined  (used to find type bool or int) */
  var tableAllAffect: iTabSymb[Instr] = new immutable.HashMap()
  /** contains boolean reegister whose value is determined, and map this value (either true or false) so that it can be propagated */
  var isBoolConstant: iTabSymb[Boolean] = new immutable.HashMap()
  var bitSize: Int = 0
  var dir: ASTB.Dir = ASTB.Left()
  /** index of current loop considered   */
  var currentLoop: Int = 0
  /** maximum number of auxiliary boolean needed */
  var maxTmp = 0
  /** map or scan parameter's expression for index i , it is null here, will be updated when an ASTBt is traversed for boolean traduction*/
  val emptyTabASTBt = immutable.HashMap.empty[String, ASTBt[B]]
  /** We will need to consult those in order to check if it is the first or the last iteration */
  var (init, step, fin) = (0, 0, 0)

  /**
   *
   * @param name register identifer
   * @return returns the value if the register is constant
   */
  def tryReadConstant(name: String): Option[ASTBt[B]] = if (isBoolConstant.contains(name)) Some(fromBoolB(isBoolConstant(name))) else None

  /**
   *
   * @param str register id
   * @return coalesced form if it exists
   */
  def coalescedIfExists(str: String) = coalesc.getOrElse(str, str)

  /**
   *
   * @param name
   * @return read x is replaced by boolean value if x is constant
   */
  def readWithConst(name: String): ASTBt[B] =
    if (isBoolConstant.contains(name)) fromBoolB(isBoolConstant(name))
    else new Read(name)(repr(B())) with ASTBt[B]

  /**
   *
   * @param s name of a register
   * @return true if s is a boolean
   */
  def isBool(s: String): Boolean =
    if (tSymbVar.contains(s)) tSymbVar(s).ringSafe == B()
    else if (coalesc.contains(s)) tSymbVar(coalesc(s)).ringSafe == B()
    else if (tableAllAffect.contains((s))) tableAllAffect(s).exps(0).asInstanceOf[ASTBg].ring == B()
    else if (tablePipelined.contains((s))) true
    else if (isBoolConstant.contains(s)) true
    else   throw new Exception("on trouve pas l'id")



  /**
   *
   * @param usedVars set of defined variable plus set of read variables, at each loop
   * @return an association of each variable to an integer corresponding to a variable used for arithmetic
   *         the required number  of such cells is simply the map size
   *         The algo follows a generic allocation strategy; reusable in other circumstances.
   *         todo turn this generic
   */
  def allocateInt(usedVars: List[(HashSet[String], HashSet[String])]): iTabSymb[Int] = {
    /**
     * adress (or register number) where a given variable will be stored,
     */
    var res: HashMap[String, Int] = HashMap()
    /**
     * heap memory, for each integer adress, stores which variable is stored or wether it is empty
     */
    var memory: ArrayBuffer[String] = //new mutable.ArrayBuffer[String](20) //I minimize the proba that it will not be enough
      mutable.ArrayBuffer.fill(20)(null)

    var liveVars: HashSet[String] = HashSet() //strings contained in buffer

    /**
     * @param valu new variables to be stored in memory
     * stores variables in memory, updates the mapping res
     */
    def place(valu: HashSet[String]): Unit = {
      var value = valu
      for (i <- 0 to memory.size - 1) {
        if (value.isEmpty)
          return
        if (memory(i) == null) {
          val e = value.head
          memory(i) = e
          value = value - e
          res = res + (e -> i)
        }
      }
      throw new Exception(" we need bigger memory")
    }

    /** remove the variables from memory */
    def unPlace(value: HashSet[String]) = {
      for (s <- value)
        memory(res(s)) = null
    }

    for ((d, r) <- usedVars) {
      place(r diff liveVars) //adds new variables defined before, read for the last time
      liveVars = liveVars.union(r)
      place(d diff liveVars) //newly defined variable d may be still in use after, we have to add them only if it was not the case
      liveVars = liveVars diff d //newly defined variable will surely not be used before their point of definition
      unPlace(d)
    }
    res
  }


  /**
   *
   * @param loop
   * @param tablePipelined
   * @return number of times a variable is used outside scan
   */
  def pipelineUseOutsideScans(loop: List[Instr], tablePipelined: iTabSymb[Instr]): iTabSymb[Int] = {
    var res: iTabSymb[Int] = HashMap()

    def update(value: AST[_]): Unit = {
      value match {
        case Read(x) =>
          if (tablePipelined.contains(x))
            res = res + (x -> (res.getOrElse(x, 0) + 1))
        case _ => value.asInstanceOf[ASTBt[_]] match {
          case Scan1(_, _, _, _, _) | Scan2(_, _, _, _, _, _) => //we consider only reads outside scan
          case _ =>
            for (exp <- value.inputNeighbors) //explore the whole tree
              update(exp)
        }
      }
    }

    for (instr <- loop)
      update(instr.exps(0))
    res
  }


  var loops: Seq[List[Instr]] = null
  var ploops: List[oneLoopInfo] = List() //collects generated data for later printing

  def firstIter(i: Int) = (i == init)

  def lastIter(i: Int) = (i + step == fin)
}


import ASTB.AffBool
import ASTB.Dir

/**
 * stores information about one loop generated by codegen, for proper display
 * @param dir direction of the loop
 * @param bitSize number of iterations
 * @param affects affectation
 * @param pipelined pipelined affectation
 * @param compiled boolean affectation
 */
class oneLoopInfo(val dir: Option[Dir], val bitSize: Int, val affects: List[Instr], val pipelined: List[Instr], val compiled: List[AffBool]) {
  override def toString = "" + bitSize

}

*/
