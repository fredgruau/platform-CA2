package compiler

import AST.{Call2, Read, isNotRead}
import ASTB.{AffBool, Elt, ParOp, Reduce, Scan1, Scan2, eltRed, fromBoolB}
import ASTBfun.{ASTBg, minSI}
import Circuit.{TabSymb, iTabSymb}
import dataStruc.DagInstr
import scala.collection.{immutable, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.mutable.ArrayBuffer

/**
 * contains all the information needed to produces ASTBt[B] code for one instruction
 *
 * @param tSymbVar needed to know the bit size and wether a variable is "arithmetic" or not
 * @param coalesc  if string is not found in tSymbvar, try to find coalesc(String)
 *                 todo do not use this class to compute the number of bit in nbitR
 **/
class CodeGen(val tSymbVar: TabSymb[InfoNbit[_]], val coalesc: iTabSymb[String] = HashMap.empty) {
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
  var pipeUs: iTabSymb[Int] = null
  /** contains all the true affects adressable, as opposed to pipelined  (used to find type bool or int) */
  var tableAllAffect: iTabSymb[Instr] = new immutable.HashMap()
  /** records boolean whose value is determined in order to propagate constants as much as possible  */
  var constant: iTabSymb[Boolean] = new immutable.HashMap()
  var bitSize: Int = 0
  var dir: ASTB.Dir = ASTB.Left()
  /** index of current loop considered   */
  var currentLoop: Int = 0
  /** maximum number of auxiliary boolean needed */
  var maxTmp = 0
  /** Contains expression of parameters */
  val env = HashMap.empty[String, ASTBt[B]]
  /** We will need to consult those in order to check if it is the first or the last iteration */
  var (init, step, fin) = (0, 0, 0)

  def tryRead(name: String): Option[ASTBt[B]] = if (constant.contains(name)) Some(fromBoolB(constant(name))) else None

  def coalescSafe(str: String) = coalesc.getOrElse(str, str)

  /** use of constant map alllows to fold constant */
  def readWithConst(name: String): ASTBt[B] =
    if (constant.contains(name)) fromBoolB(constant(name))
    else new Read(name)(repr(B())) with ASTBt[B]

  /** boolean variable do not get an integer sufx added */
  def isBool(s: String): Boolean =
    if (tSymbVar.contains(s)) tSymbVar(s).ringSafe == B()
    else if (coalesc.contains(s)) tSymbVar(coalesc(s)).ringSafe == B()
    else if (tableAllAffect.contains((s))) tableAllAffect(s).exps(0).asInstanceOf[ASTBg].ring == B()
    else if (tablePipelined.contains((s))) true
    else if (constant.contains(s)) true
    else
      throw new Exception("on trouve pas l'id")

  /** return the number of times on which we iterate */
  private def nbitLoop(loopAffSup: List[Instr]) = {
    val expAff0 = loopAffSup(0).exps(0).asInstanceOf[ASTBg] //we focus on one of the affect expression
    val expInt = //for reduce and elt we need to first get the underlying integer expression
      expAff0 match {
        case e@(Reduce(_, _, _) | Elt(_, _)) => e.inputNeighbors(0)
        case _ => expAff0
      }
    expInt.asInstanceOf[ASTBg].nBit(this, env) //we might need to compute the number of bit of subexpression and that in turn necesseitates to consult the environement
  }

  /**
   *
   * @param usedVars set of defined variable plus set of read variables, at each stages
   * @return an association of each variable to an integer corresponding to a variable used for arithmetic
   *         the required number  of such cells is simply the map size
   *         The algo follows a generic allocation strategy; reusable in other circumstances.
   *         todo turn this generic
   */
  def allocateInt(usedVars: List[(HashSet[String], HashSet[String])]): iTabSymb[Int] = {
    var res: HashMap[String, Int] = HashMap()
    var memory: ArrayBuffer[String] = //new mutable.ArrayBuffer[String](20) //I minimize the proba that it will not be enough
      mutable.ArrayBuffer.fill(20)(null)

    var liveVars: HashSet[String] = HashSet() //strings contained in buffer
    /** put new variables in memory, updates the mapping res */
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


  /** computes the number of times a variable is used outside scan */
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

  /**
   * transform an integer affectation into a list of pure boolean affectations
   * updates many global variables to be consulted, including the symbol table which allows to computes bit size
   * * @param inst integer affectation
   *
   * @return each List of the list can be computed in parallel
   */
  var loops: Seq[List[Instr]] = null
  var ploops: List[Lop] = List() //collects generated data for later printing
  def codeGen(inst: Instr): List[List[ASTBt[B]]] = {
    val exp = inst.exps(0).asInstanceOf[ASTBg]
    val decall = exp.deCallify(env, tSymbVar)
    //println("\n"+decall.toStringTree)
    val af = Affect(inst.names(0), decall) //reconstruit l'affectation sans les calls
    val dagi = new DagInstr(List(af))
    dagi.dagAst.addGenerators(List(decall)) //add all subtree of mapscan to dags
    val iT1: collection.Set[AST[_]] = dagi.inputTwice.filter(isNotRead)
    val iT = iT1.filter(ASTB.isNotMap1Read(iT1)) //we could filter out more stuff because it consumes register and registers are a precious ressource
    val redEltSet = dagi.dagAst.visitedL.filter(eltRed).toSet //affectify reduction because they will be executed as parallel loops
    val chDir = decall.SetDirAndReturnChangedDir()
    val toBeReplaced = iT.union(redEltSet).union(chDir.asInstanceOf[Set[AST[_]]])
    val toBeRepl: List[AST[_]] = dagi.dagAst.visitedL.filter(a => toBeReplaced(a) && isNotRead(a));
    toBeRepl.map(_.setNameIfNull3());
    val dagis = dagi.affectIfy(toBeReplaced) //it is possible that some of the subtrees have "Both()" as direction
    //println(dagis)
    loops = dagis.packetize4ASTB(Instr.isBoolean).reverse //distribute all the affectation in parallel loops
    //println(loops)
    var codeNloop = List[List[ASTBt[B]]]()
    var code1loop = List[ASTBt[B]]()

    /** all the non-pipelined integer or boolean affectation */
    tableAllAffect = new immutable.HashMap()
    tableAllPipelined = new immutable.HashMap()
    var liveVars: List[(HashSet[String], HashSet[String])] = List()
    for (loop <- loops) { //todo when coalescing,  care should be taken that temporary variables used in the computation of one loop can reused in the next loop
      val affects: List[Instr] = dagis.sup(loop)
      tableAllAffect ++= affects.map((is: Instr) => is.names(0) -> is)
      val dir1 = ASTB.dir2(affects(0))
      if (dir1 == None) { //affectation has to be boolean, if dir1 is both we see indexes -1 appearing
        assert(affects.size == 1) //boolean affectation are singleton class
        assert(nbitLoop(affects) == 1) //they do not make use of integers so no pipeline
        code1loop = List(affects(0).codGen(-1, this, env)) //we put -1 to trigger an error should it not be boolean.
        // that is already a final boolean instruction but we may need to fold constant
        ploops ::= new Lop(None, 1, affects, List(), code1loop.asInstanceOf[List[AffBool]])
      }
      else {
        dir = dir1.get //is the loop leftwared or rightward,
        dir = dir.narrowed // it could still be undertermined this is why we apply  narrowed,
        code1loop = List() //initialise the code for the current loop.
        pipelined = loop.toSet.diff(affects.toSet) //affectation pipelined means the name is instanciated only once// as opposed to as many times as the number of bits
        tablePipelined = new immutable.HashMap() ++ pipelined.map((is: Instr) => is.names(0) -> is)
        tableAllPipelined ++= tablePipelined //we need to evaluate the number of bits... a bit awkward we add better computes a symbol table to avoid traversing the tree each time we read the values
        bitSize = nbitLoop(affects)
        if (dir == ASTB.Left()) {
          init = 0;
          step = 1;
          fin = bitSize
        }
        else if (dir == ASTB.Right()) {
          init = bitSize - 1;
          step = -1;
          fin = -1
        }
        else throw new Exception("direction should have been narrowed to Left or right")
        evaluated = new HashMap[String, Int]() ++ pipelined.map(_.names(0) -> (init - step)) //ce sont des compteurs mis à zéro
        pipeUs = pipelineUseOutsideScans(loop, tablePipelined)
        var i = init
        do {
          for (af <- affects) {
            val newAf = af.codGen(i, this, env)
            code1loop = newAf.affBoolify().reverse ::: code1loop //affBoolify will remove uncessary calculation when elt is applied
            //the reverse's goal is to maintain the same order which had been reverse in this way of computation with list
          }
          i = i + step
        }
        while (i != fin)
      }
      val names: (HashSet[String], HashSet[String]) = ASTB.tmpNames(code1loop)
      //  println(names)
      codeNloop = code1loop.reverse :: codeNloop
      ploops ::= new Lop(Some(dir), bitSize, affects, pipelined.toList, code1loop.reverse.asInstanceOf[List[AffBool]])
      liveVars ::= names
    }
    val coalescTable: iTabSymb[String] = allocateInt(liveVars).map((x: (String, Int)) => (x._1 -> ("r" + x._2)))

    //println(coalescTable)
    val coalesced = codeNloop.map(_.map(_.coalesc(coalescTable)))
    coalesced.reverse
    codeNloop.reverse
  }

  def firstIter(i: Int) = (i == init)

  def lastIter(i: Int) = (i + step == fin)
}

