package compiler

import compiler.AST.Read
import compiler.ASTB.{Dir, Elt, False, Reduce, Scan1, Scan2, True, affBoolConst, fromBoolB}
import compiler.ASTBfun.ASTBg
import compiler.Circuit.{TabSymb, iTabSymb}
import dataStruc.{Named, WiredInOut}

import scala.collection.immutable
import scala.collection.immutable.HashMap

/**
 *
 * @param instrs the instructions that can be executed in a single loop, and that we will compiled
 * @param tSymbVar      needed to find about bit size
 * @param coalesc
 * @param constantTable contains constant values, in order to fold constants
 * @param boolAST       binary code with boolean operators, as a List of ASTBt[B] is sometimes empty, I do not get why
 * @param boboolAST     binaryCode with coalesced registers.
 */
abstract class Packet(val instrs: List[Instr],
                      val tSymbVar: TabSymb[InfoNbit[_]], val coalesc: iTabSymb[String], val constantTable: TabSymb[Boolean],
                      var boolAST: List[ASTBt[B]] = List(), var boboolAST: List[ASTBt[B]] = List()) extends WiredInOut[Packet] {

  /** names of tmp   variables used by instruction. */
  def usedVars() = ASTB.used(boolAST).filter(ASTB.isTmp(_)).toSet

  /** names of tmp variables produced by instruction. */
  def names: List[String] = ASTB.names(boolAST).filter(ASTB.isTmp(_)).toList


  /** we need to find out if int variable are live after packet evaluation, because used in another packet
   * because then the memory occupied cannot be liberated */
  var tmpIntLiveVarsAfter: Set[String] = null

  /**
   *
   * @param tmpLiveVars tmpVariable lived after the loops
   * @return tmpLiveVars tmpVariable lived just before the loops
   */
  def tmpLiveBefore(tmpLiveVars: Set[String]): Set[String] = {
    /**
     *
     * @return list of temporary variables defined in the packet
     */
    def definedTMPint: Set[String] = instrs.map(_.names(0)).filter(ASTB.isTmp(_)).toSet

    /** @return list of temporary variables used in the packet
     */
    def usedTMPint: Set[String] = instrs.flatMap(_.usedVars()).toSet.filter(ASTB.isTmp(_))

    tmpIntLiveVarsAfter = tmpLiveVars
    tmpLiveVars.union(usedTMPint).diff(definedTMPint)
  }

  val info: String
  val affected: String //generated  affectation

  /** print binary code if non empty */
  def binary = if (boolAST.nonEmpty) "\nBinary() " + boolAST.map(_.toStringTree).mkString(" |_| ")

  /** print coalesced binary code if non empty */
  def binaary: String = if (boboolAST.nonEmpty)
    "\nBinaary() " + boboolAST.map(_.toStringTree).mkString(" |_| ") else
    "emptyyy"


  override def toString = info + affected + binary + binaary


  /**
   * @return list of boolean affectations compiling one packet of integer instructions.
   *         implementation differs depending if we have a pure boolean instruction (BitNoLoop) or an integer instruction (BitLoop)
   */
  def unfoldInt(): List[ASTBt[B]]

  /**
   *
   * @return replaces variables in BoolAst by their coalesced form
   */
  def coalesc(c: iTabSymb[String]): List[ASTBt[B]] =
    boolAST.map(_.coalesc(c))

  /**
   * will store the boolification in the boolAst field, for future printing and code generation
   */
  def addUnfoldInt() = {
    boolAST = unfoldInt().reverse.filter(e => e != False() && e != True()) //whole expression may reduce to False() or True() after simplification. We remove those débris
  } // unfoldInt return affectations in reverse order because last affectation are inserted on the head, so it must be reversed

  def addCoalesc(c: iTabSymb[String]) = {
    boboolAST = coalesc(c)
  }

  def isBool(s: String): Boolean =
    if (tSymbVar.contains(s))
      tSymbVar(s).ringSafe == B()
    else if (coalesc.contains(s)) tSymbVar(coalesc(s)).ringSafe == B()
    else if (constantTable.contains(s)) true
    else throw new Exception("on trouve pas l'id")

  /**
   *
   * @param name
   * @return read x is replaced by boolean value if x is constant
   */
  def readWithConst(name: String): ASTBt[B] =
    if (constantTable.contains(name)) fromBoolB(constantTable(name))
    else new Read(name)(repr(B())) with ASTBt[B]

  def totalOp = {
    boolAST.map(_.totalOp).foldLeft(0)(_ + _)
  }

}


object Packet {

  /** This class BitNoLoop is used if the packet is a singleton instruction that inputs only boolean and produces boolean
   * When analysing the direction of the loop, it returned None. It  is already in boolean form,
   * so it could be reproduced as is, but traversing it allows to simplify it if possible */
  class BitNoLoop(instr: Instr,
                  override val tSymbVar: TabSymb[InfoNbit[_]], override val coalesc: iTabSymb[String],
                  override val constantTable: TabSymb[Boolean])
    extends Packet(List(instr), tSymbVar, coalesc, constantTable) {
    val info = "No-Loop()     "
    val affected = "affected " + instr

    override def toString = info + affected //binary is the same as affected, so there is no need to reproduce it

    /**
     *
     * @param x variable to be read
     * @return may return a constant instead of a read
     */
    def read(x: String): ASTBt[B] = {
      assert(tSymbVar.contains(coalesc.getOrElse(x, x)) || Named.isTmp(x)
        , "could not find" + x) //x has to be a register generated during spatial unfolding
      //it could also be a temporary arithmetic variable generated for a previous loop
      readWithConst(x)
    }

    /**
     *
     * @return single boolean affectations
     *         for e a pure boolean instruction (BitNoLoop) the list is a singleton
     */
    override def unfoldInt(): List[ASTBt[B]] = {
      val expr = instr.exps(0).asInstanceOf[ASTBt[B]]
      List(expr.boolExprNoIndex(this, instr.names(0), immutable.HashMap.empty[String, ASTBt[B]]))
    }
  }

  /**
   * Stores the info about one elementary packet that can be compiled as a single loop
   * an instruction itself is compiled into a list of such loop
   *
   * @param dir      wether we go from left to right or the reverse
   * @param loopSize number of loop iterations
   * @param affects  variables set by the loops
   * @param instrs   the instructions part of the loop
   */
  class BitLoop(override val tSymbVar: TabSymb[InfoNbit[_]],
                override val coalesc: iTabSymb[String], override val constantTable: TabSymb[Boolean], val dir: Dir, val loopSize: Int, val affects: List[Instr],
                override val instrs: List[Instr], val init: Int, val step: Int, val fin: Int,
               ) extends Packet(instrs, tSymbVar, coalesc, constantTable) { //TODO the order matters between affects and pipelined
    /* display  direction and number of iterations of loop */
    val info = dir + " " + loopSize + " bits "
    /* display the instruction in topological order, starting with the pipelined if any, and avoiding redundant display*/
    val pipelined: Seq[Instr] = instrs.filter(!affects.toSet.contains(_)) //all the instructions not leading to affectation, will be pipelined.
    //variables computed and then consumed during the loops, we do not need to instantiate,    except if they are live after the pacquet.
    val affected = (if (pipelined.nonEmpty) "pipelined" + pipelined.reverse.mkString("\n                      ") + "\n              " else "") +
      "affected " + affects.mkString("\n                       ") //print pipelined in the right order. we put many space characters to obtain a correct alinement
    /** allows to quickly find if a variable is pipelined */
    val pipelinedTable = new immutable.HashMap() ++ pipelined.map((is: Instr) => is.names(0) -> is)
    /** evaluated(x)=i iff pipelined affectation x<-exp has been done for itération i. */
    var evaluated: iTabSymb[Int] = new HashMap[String, Int]() ++ pipelined.map(_.names(0) -> (init - step))
    /**
     * number of times a variable is used outside scan
     */
    var pipelineUseOutsideScans: iTabSymb[Int] = HashMap()

    /**
     * local function used to compute pipelineUseOutsideScans
     *
     * @param value AST to be processed
     */
    private def update(value: AST[_]): Unit = {
      value match {
        case Read(x) =>
          if (pipelinedTable.contains(x))
            pipelineUseOutsideScans = pipelineUseOutsideScans + (x -> (pipelineUseOutsideScans.getOrElse(x, 0) + 1))
        case _ => value.asInstanceOf[ASTBt[_]] match {
          case Scan1(_, _, _, _, _) | Scan2(_, _, _, _, _, _) => //we consider only reads outside scan
          case _ =>
            for (exp <- value.inputNeighbors) //explore the whole local loop
              update(exp)
        }
      }
    }

    for (instr <- instrs) update(instr.exps(0))

    /**
     *
     * @param s variable name
     * @return true if implemented as a boolean. if s is lived after the instruction, then the integer must be stored, and
     *         therefore implemented  as an integer, not as a boolean
     */
    override def isBool(s: String): Boolean =
      if (pipelinedTable.contains((s)) && !tmpIntLiveVarsAfter.contains(s)) true else super.isBool(s) //now we know also of super!!

    /**
     *
     * @param x name of scalar variable
     * @param i loop index
     * @return returns x plus i if non boolean,  so as to generate a different register for each loop index
     *         checking if boolean requires the use many tables.
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

    /**
     *
     * @param x variable considered
     * @param i current loop index considered
     * @return optional suffix i added if x is live after loop
     */
    def checkLiveforAddIndex(x: String, i: Int): String =
      if (tmpIntLiveVarsAfter.contains(x)) //if x is gonna be reused in another packet, we need to store the components individually
      addSufx(x, i)
      else
      x

    /**
     *
     * @param i considered index
     * @return true if it is the first index
     */
    def firstIter(i: Int) = (i == init)

    /**
     *
     * @param i considered index
     * @return true if it is the last index of the iteration
     */
    def lastIter(i: Int) = (i + step == fin)

    /**
     *
     * @param x   variable
     * @param i   index considered
     * @param env effective parameters, in order to find out about bit size
     * @return x[i] or if not yet computed, the code of the expression x[i]
     */
    def readAtIndex(x: String, i: Int, env: HashMap[String, ASTBt[B]]): ASTBt[B] = {
      if (pipelinedTable.contains(x)) { //it is a pipelined variables!
        if (evaluated(x) * step > i * step)
          throw new Exception("when a map is combined with a scan with initused, the scan must comes first for pipelining to work!!")
        //with initused, it is the map which will first read the pipelined array, the scan will not.
        if (evaluated(x) * step < i * step) { //means that we have not yet compiled x's pipelined expression
          evaluated += (x -> i) //register the fact that yes now we 'll compile it
          val newExp = pipelinedTable(x).exps(0).asInstanceOf[ASTBg].boolifyForIndexI(i, this, null, env) //compiles it
          val s: String = if (!tmpIntLiveVarsAfter.contains(x) && lastIter(i) && pipelineUseOutsideScans(x) == 1)
            null else x //for last iteration, a pipelined variable used once need not be stored, exept if the pipelined is reused in another loop
          affBoolConst(checkLiveforAddIndex(s, i), newExp, this)
        }
        else readWithConst(checkLiveforAddIndex(x, i))
      }
      else {
        assert(tSymbVar.contains(coalesc.getOrElse(x, x)) || Named.isTmp(x), "could not find" + x)
        //x has to be a register generated during spatial unfolding
        //it could also be a temporary arithmetic variable generated for a previous loop
        readWithConst(addSufx(x, i))
      }
    }


    /**
     * here we have to distinguish between pipelining operators, scalar operators, ...
     *
     * @return list of boolean affectations compiling one packet of integer instructions.
     *         in case of Base2, many affectations will have to be generated.
     *
     */
    override def unfoldInt(): List[ASTBt[B]] = {
      var i = init
      var result: List[ASTBt[B]] = List()
      do {
        for (af <- affects) {
          val newAf = af.boolExprForIndexI(i, this, immutable.HashMap.empty[String, ASTBt[B]]) //works only for pipelined operators
          result = newAf.affBoolify().reverse ::: result //affBoolify will remove uncessary calculation when elt is applied
          //the reverse's goal is to maintain the same order which had been reverse in this way of computation with list
        }
        i = i + step
      }
      while (i != fin)
      result = result.filter(e => e != False() && e != True()) //sometimes true or false do not get simplified and appear as leftover debris that we should remove
      result // contains boolean register affectation to interpret one affectation
    }

  }

  /**
   *
   * @param loopAffSup packet of instructions using integer with the same number of bits
   * @return this number of bits, wich will correspond to the number of iteration of the loop
   */
  private def nbitLoop(loopAffSup: List[Instr], t: TabSymb[InfoNbit[_]], c: iTabSymb[String]) = {
    val expAff0 = loopAffSup(0).exps(0).asInstanceOf[ASTBg] //we can  focus on one of the affect expression
    val expInt = //for reduce and elt we need to first get the underlying integer expression
      expAff0 match {
        case e@(Reduce(_, _, _) | Elt(_, _)) => e.inputNeighbors(0)
        case _ => expAff0
      }
    //expInt.asInstanceOf[ASTBg].nBit(this, emptyTabASTBt) //we might need to compute the number of bit of subexpression and that in turn necessitates to consult the environement
    //c'est ici que c'est pas clean, car on réutilise un truc qu"etait pas fait pour ca au depart
    ASTB.nbitExp2(immutable.HashMap[AST[_], Int](), expInt.asInstanceOf[ASTBg], t, c)
  }


  /**
   *
   * @param instrs instructions that can be evaluated in a single loop
   * @return a Packet, either a BitNoLoop if the packet contains a single pure boolean affectation, or else a BitLoop
   */
  def apply(instrs: List[Instr], t: TabSymb[InfoNbit[_]], c: iTabSymb[String], const: TabSymb[Boolean]): Packet = {
    val remainAsAffects: List[Instr] = WiredInOut.sup2(instrs)
    assert(remainAsAffects.nonEmpty) //there could be no pipelined, but there is allways at least one affect
    val dirLoop = ASTB.instrDirection(remainAsAffects(0))
    val loopSize = nbitLoop(remainAsAffects, t, c)
    if (dirLoop == None) { //affectation has to be boolean, computed from boolean, this case is particular
      assert(remainAsAffects.size == 1) //pure boolean affectation are singleton class
      assert(loopSize == 1) //they do not make use of integers so no pipeline
      new BitNoLoop(instrs(0), t, c, const)
    }
    else {
      val dir = dirLoop.get.narrowed
      val pipelined = instrs.filter(!remainAsAffects.toSet.contains(_)) //all the instructions not leading to affectation, will be pipelined.
      val (init, step, fin) = dir match {
        case ASTB.Left() => (0, 1, loopSize)
        case ASTB.Right() =>
          (loopSize - 1, -1, -1) //changed very recently first assing is 2 for integer on three bits, last assign is zero
        case _ => throw new Exception("direction should have been narrowed to Left or right")
      }
      new BitLoop(t, c, const, dir, loopSize, remainAsAffects, instrs, init, step, fin)
    }


  }


}