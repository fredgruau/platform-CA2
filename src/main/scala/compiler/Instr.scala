package compiler

import AST._
import ASTB.{AffBool, Uint}
import ASTBfun.{ASTBg, concat2UI, redop}
import Instr._
import VarKind._
import dataStruc.{Align2, Dag, DagInstr, DagNode, HeapStates, WiredInOut}
import Circuit._
import compiler.SpatialType.{ASTLtG, IntV, UintV}
import compiler.Packet.BitLoop
import dataStruc.Align2.{compose, invert}

import scala.language.postfixOps
import scala.collection.{mutable, _}
import scala.collection.immutable.{HashMap, HashSet}

/** Instruction used within the compiler, call, affect. Dag and Union allows to defined ConnectedComp  */
abstract class Instr extends DagNode[Instr] with WiredInOut[Instr] {
  def simplifConcat(): Instr = null

  /** substitute x in names and x in read(x) by coalesc(x) */
  def coalesc(allCoalesc: iTabSymb[String]): Instr = null

  /**
   *
   *
   * @param heap       initial state of heap
   * @param funs       function that could be called
   * @param occupied   number of global variables
   * @param allCoalesc corespondance between formal parameters, and effective parameter including also  memory adresses
   * @return
   */
  def codeGenInstr(heap: Vector[String], funs: iTabSymb[DataProgLoop[_]], occupied: Int, allCoalesc: iTabSymb[String]): List[CallProc] = null

  /**
   *
   * @param t symbol table, to get the bitsize
   * @return a list  of Boolean Instruction compiling the integer instruction,
   *         also updates t adding the boolean elements of integers
   */
  def unfoldInt(t: TabSymb[InfoNbit[_]]): List[Instr]


  def radiusify3(radius: TabSymb[Int], tSymbVar: TabSymb[InfoNbit[_]]): Instr = {
    null
  } //implemented only in  Affect

  /*
    def radiusify(radius: TabSymb[(Int, Option[Modifier])], tSymbVar: TabSymb[InfoNbit[_]]): Unit = {}

    def radiusify2(radius: TabSymb[Int], tSymbVar: TabSymb[InfoNbit[_]]): Unit = {}
  */

  protected def show(x: Option[Locus]) = x match {
    case Some(s) => "" + s
    case None => ""
  }

  protected def show2(x: Option[Ring]) = x match {
    case Some(s) => "" + s
    case None => ""
  }


  def boolExprForIndexI(i: Int, gen: BitLoop, env: HashMap[String, ASTBt[B]]): ASTBt[B] = null //only defined for affect!

  def detm1ise(muName: String): Instr = if (names(0) != muName) this
  else new Affect(muName, exps(0).asInstanceOf[ASTBt[Ring]].detm1ise)


  /** removes the first tm1 which we now verify is here */
  def detm1iseHead: Instr = {
    val newExp = exps(0).asInstanceOf[ASTBg] match {
      case e@ASTB.Tminus1(a) => a.name = e.name; a
      case _ =>
        throw new Exception("should begin with tm1"); null
    }
    new Affect(names(0), newExp)
  }

  /** recursive removes the first tm1 */
  def detm1iseR: Instr = {
    new Affect(names(0), exps(0).asInstanceOf[ASTBt[Ring]].detm1iseR)
  }

  /**
   *
   * @param x instruction input neighbor of  this
   * @return true if for example this.name is "shifttoto" and x's name is "toto"
   */
  def shiftandshifted(x: Instr) = isShift && (x.names(0) == unShifted)

  def unShifted = names(0).drop(5)

  def myZone2(tZone: Map[String, Zone], myRoot: Map[String, Instr]) =
    tZone(myRoot(names.head).names.head)

  def isFolded2(tZ: Map[String, Zone], myRoot: Map[String, Instr]) = myZone2(tZ, myRoot).folded

  def inputFolded2(tZ: Map[String, Zone], myRoot: Map[String, Instr]) = inputNeighbors.head.isFolded2(tZ, myRoot)

  def mySchedule2(tZ: Map[String, Zone], myRoot: Map[String, Instr], align2Root: Map[String, Array[Int]]): Array[Int] = {
    // if(names(0)=="distTslope")     printf("jysuis\njysuis\njysuis\njysuis\njysuis\njysuis\njysuis\njysuis\njysuis\n")
    val ps = myZone2(tZ, myRoot).pickedSchedule //schedule of root which is aux5 must be O51324
    val a = align2Root(names.head) //alignement to root must be 240513 for distTslope
    val res = if (a != null) compose(ps, invert(a)) else null //must give 234501 will be null for shift instr
    res
  }

  /**
   * redefined in callProc
   *
   * @return
   */
  def callProcToAffect: Instr = this

  def tobeProcessedInMacro: Boolean = false

  def isReturn: Boolean = this match {
    case CallProc("return", _, _) => true;
    case _ => false
  }

  def exps: List[AST[_]]

  /**
   *
   * @param id1 rewriting of AST
   * @return instruction where rewriting has been applied on all expressions.
   */
  def propagate(id1: rewriteAST2): Instr

  def aligned = !alignPerm.isEmpty //faut se mefier, ca va pas marcher pour load?


  /** true for instruction part or Transfer Connected Components */
  def isTransfer: Boolean = {
    throw new RuntimeException("test isTransfer is done only in Affect instruction ")
  }

  /** @return the locus of expressions, for affectation. */
  def locus: Option[Locus] = None

  def ring: Option[Ring] = None

  def isV = locus.get == V()

  /** to be set if we want to use the Align feature, contains an alignment towards each usedvars of the instr (indexed by their name) */
  var alignPerm: iTabSymb[Array[Int]] = Map.empty

  /**
   * @return alignement from this to n.   */
  def neighborAlign(n: Instr): Array[Int] = {
    if (alignPerm.isEmpty)
      null
    else if (alignPerm.contains(n.names.head)) //n is a used var of this, so "this" is an element of n.neighbor,
    alignPerm(n.names.head) //neighborAligned(n.names(0))  is an alignement from "this" to n,
    else if (n.alignPerm.contains(names.head)) //otherwise, it must be the opposite i.e. this is a used var of n. we find an alignement from n to "this", we invert
    Align2.invert(n.alignPerm(names.head))
    else throw new RuntimeException(" Not find alignement ")
  }

  // val exp:AST[T]
  /** @param hd head
   * @param tl  and tail  are built, in order to  find out the id of formal parameter passed by results. */
  def buildhdtl(hd: TabSymb[String], tl: TabSymb[String]): Unit = this match {
    case Affect(_, exp) => exp match {
      case Heead(Read(s)) => hd += s -> exp.name
      case Taail(Read(s)) => tl += s -> exp.name
      case _ =>
    }
    case _ =>
  }

  /**
   *
   * @param hd list names associated to head
   * @param tl list of names associated to tail
   * @param t  symbol table
   * @return Replaces instruction of the form Affect(Call ..) expressions, by callProc instructions.
   *         Remove head and tail operations which have become useless, and return instructions.
   */
  def procedurIfy(hd: TabSymb[String], tl: TabSymb[String], t: TabSymb[InfoType[_]]): List[Instr] = {
    /**
     * @param s
     * @return names of ASTL variables, associated to variable of type cons(cons...))
     */
    def subNames(s: String): List[String] = if (hd.contains(s)) hd(s) :: subNames(tl(s)) else List(s)

    /**
     *
     * @param arg one of the argument of call
     *            if the name of arg is null, it sets it to auxL and adds it to the symbol table with apropriate type
     *            and with store as kind
     */
    def setNameIfNullandAddtoT(arg: AST[_]) = {
      if (arg.name == null) {
        arg.setNameIfNull("auxl")
        t += arg.name -> new InfoType(arg.mym, StoredField())
      }
    }

    this match {
      case Affect(s, exp) => exp match {
        case c: Call[_] =>
          val res = subNames(s)
          // we must set names of effective parameters and add them to the symbol table if needed
          c.args.toList.map(setNameIfNullandAddtoT(_))
          //value which are sent through call and retrieved from the procedure, have to be stored
          for (r <- res ::: c.args.toList.map(_.name))
            if (t.contains(r) && t(r).k == MacroField()) t += r -> new InfoType(t(r).t, StoredField()); // register the fact that results must be stored.
          List(CallProc(c.f.name, res, c.args.toList))
        case Taail(_) | Heead(_) => List() //we do not need those any more.
        case _ => List(this)
      }

      case _ => if (this.isReturn) List() else List(this)
    }
  }

  def procedurIfyOld(hd: TabSymb[String], tl: TabSymb[String], t: TabSymb[InfoType[_]]): List[Instr] = {
    /**
     * @param s
     * @return names of ASTL variables, associated to variable of type cons(cons...))
     */
    def subNames(s: String): List[String] = if (hd.contains(s)) hd(s) :: subNames(tl(s)) else List(s)

    /**
     *
     * @param arg one of the argument of call
     *            if the name of arg is null, it sets it to auxL and adds it to the symbol table with apropriate type
     *            and with store as kind
     */
    def setNameIfNullandAddtoT(arg: AST[_]) = {
      if (arg.name == null) {
        arg.setNameIfNull("auxl")
        t += arg.name -> new InfoType(arg.mym, StoredField())
      }
    }

    this match {
      case Affect(s, exp) => exp match {
        case c: Call[_] =>
          val res = subNames(s)
          // we must set names of effective parameters and add them to the symbol table if needed
          c.args.toList.map(setNameIfNullandAddtoT(_))
          //value which are sent through call and retrieved from the procedure, have to be stored
          for (r <- res ::: c.args.toList.map(_.name))
            if (t.contains(r) && t(r).k == MacroField()) t += r -> new InfoType(t(r).t, StoredField()); // register the fact that results must be stored.
          List(CallProc(c.f.name, res, c.args.toList))
        case Taail(_) | Heead(_) => List() //we do not need those any more.
        case _ => List(this)
      }

      case _ => if (this.isReturn) List() else List(this)
    }
  }

  /**
   *
   * @param cur        The current programm
   * @param expBitSize mutable map, Stores number of bits of sub expressions.
   * @param newTSymb   The symbol table with number of bits
   * @param newFuns    Functions generated
   * @return The instructions rewritten so as to include Extend where necessary.
   */
  def bitIfy(cur: DataProg[InfoType[_]], expBitSize: AstMap[Int], newTSymb: TabSymb[InfoNbit[_]], newFuns: TabSymb[DataProg[InfoNbit[_]]]): Instr = this match {
    case Affect(s, exp) =>
      val newExp = exp.asInstanceOf[ASTLt[_, _]].bitIfyAndExtend(cur, expBitSize, newTSymb)
      newTSymb += s -> new InfoNbit(cur.tSymbVar(s).t, cur.tSymbVar(s).k, expBitSize(newExp));
      Affect(s, newExp).asInstanceOf[Instr]
    case CallProc(f, names, exps) =>
      val newexps = exps.map(_.asInstanceOf[ASTLt[_, _]].bitIfyAndExtend(cur, expBitSize, newTSymb))
      val nbitarg = newexps.map(a => expBitSize(a)) //.toList.flatten
      val newname = f + nbitarg.map(_.toString).foldLeft("")(_ + "_" + _) //we make precise in the function name, the number of bits of arguments

      //  if (f.size>2 && sysInstr.contains(f.substring(0,3)))
      if (isSysInstr(f))
      //there is not code to be generated for system calls
      CallProc(f, names, newexps).asInstanceOf[Instr]
      else {
        if (!newFuns.contains(newname))
          newFuns += (newname -> cur.funs(f).bitIfy(nbitarg))
        // re-creates the code of f, taking into account nbitarg.
        val fprog = newFuns(newname)
        val nbitResult = fprog.paramR.map(s => fprog.tSymbVar(s).nb) //we get the number of bits of results
        (names zip nbitResult).foreach { sn => newTSymb += sn._1 -> new InfoNbit(cur.tSymbVar(sn._1).t, cur.tSymbVar(sn._1).k, sn._2) }
        CallProc(newname, names, newexps).asInstanceOf[Instr]
      }
  }


  // TabSymb[InfoNbit[_]]
  /** we add one (resp. two) suffixes, for simplicial (resp. transfer) variables  */
  def unfoldSpace(m: Machine, tSymb: TabSymb[InfoNbit[_]]): List[Instr] =
    this match {
      case Affect(v, exp) => // println(exp.toStringTree) ;
        val exp2 = exp.asInstanceOf[ASTLt[_, _]]

        //processing redop separately

        exp2.locus match {
          case s: S => s.deploy(v).zip(exp2.unfoldSimplic(m)).map({ case (suf, e) => Affect(suf, e) }).toList

          //case s: S => s.sufx.zip(exp2.unfoldSimplic(m)).map({ case (suf, e) => Affect(v + "$" + suf, e) }).toList
          case l@T(s1, _) =>
            val exp2unfolded = exp2.unfoldTransfer(m)
            val s1zip = s1.sufx.zip(exp2unfolded)
            s1zip.map({
              case (suf1, t) =>
                val secondZip = l.sufx.zip(t).map({ case (suf2, e) => Affect(v + "$" + suf1 + suf2, e) }).toList
                secondZip
            }).toList.flatten
        }
      case CallProc(f, n, e) => List(CallProc(f, n.flatMap(Instr.deploy(_, tSymb)),
        e.asInstanceOf[List[ASTLt[_, _]]].flatMap(_.unfoldSpace(m)))) //tSymb(n).t._1
    }

  def locus2: Option[Ring] = None


}


/**
 * call of a procedure,
 * where several parameters can be passed by result.
 *
 * @param procName procedure's' name
 * @param names    names of values produced by procedure.
 * @param exps     passed as data
 */
case class CallProc(var procName: String, names: List[String], exps: List[AST[_]]) extends Instr {
  override def callProcToAffect: Instr = if (tobeProcessedInMacro) new Affect(names(0), exps(0))
  else throw new Exception("only memo callProc gets macroified");


  override def tobeProcessedInMacro =
    isProcessedInMacro(procName)

  // override def namesDefined: List[String] = if() List()

  /**
   * for bug and show we will add the name of the motherLayer to the name of the call
   *
   * @param motherLayer : Layer to which the bug or the show is attached
   */
  def preciseName(motherLayer: String) = procName += motherLayer


  override def toString: String = {
    val y=0
    pad(names.mkString(","), 25) + "<-" + procName + "(" + exps.map(_.toStringTree).mkString(" ") + ")"
  }


  //override def toString: String = pad(names.foldLeft(" ")(_ + "," + _).substring(2), 25) + "<-" + p + "(" + exps.map(_.toStringTree).foldLeft(" ")(_ + " " + _) + ")\n"

  /**
   *
   * @return variables name used by the instruction
   */
  def usedVars(): HashSet[String] = exps.map(_.symbolsExcepLayers).foldLeft(immutable.HashSet.empty[String])(_ | _)


  override def propagate(id1: rewriteAST2): Instr = {
    val newInstr = CallProc(procName, names, exps.map((a: AST[_]) => id1(a)))
    newInstr
  }

  /**
   *
   * @param t symbol table, to get the bitsize
   * @return a list  of Boolean Instruction compiling the integer instruction,
   *         also updates t adding the boolean elements of integers
   */
  override def unfoldInt(t: TabSymb[InfoNbit[_]]): List[Instr] = {
    val newExps: List[List[ASTBt[B]]] = exps.asInstanceOf[List[ASTBg]].map(_.deCallify(HashMap.empty[String, ASTBt[B]]).unfoldInt(t))

    var resb: List[String] = List()
    for (nameInt <- names) {
      val boolNames = deployInt2(nameInt, t(nameInt))
      resb = resb ::: boolNames
      for (boolName <- boolNames) {
        if (!t.contains(boolName)) //if name is already in symbol table, adding it anew will replace a spatial type by a scalar type
        // or will remove the layer info, which in total will loose information so we do not want that
        t.addOne(boolName -> new InfoNbit[B](B(), t(nameInt).k, 1)) //can be either of StoredField, paramR, paramD??
      }
    }

    /*    val boolNames=names.flatMap((name:String)=>deployInt(name,t(name).nb))
        boolNames.map((bname:String)=>
          if(!t.contains(bname)) //if name is already in symbol table, adding it anew will replace a spatial type by a scalar type
            //or will remove the layer info, which in total will loose information so we do not want that
          t.addOne(bname->new InfoNbit[B](B(), t(name),1))) //adds scalar variables. should we?*/
    val res = List(new CallProc(procName, resb, newExps.flatten))
    res
    //if(p=="memo") //we can generate a list of memo

  }

  /**
   * list of calls generated from a call to either a CA loop or list of calls
   *
   * @param heap       initial state of heap
   * @param funs       function that could be called
   * @param occupied   number of global variables
   * @param allCoalesc corespondance from formal parameters, to effective parameters, including  also memory adresses
   * @return
   */
  override def codeGenInstr(heap: Vector[String], funs: iTabSymb[DataProgLoop[_]], occupied: Int, allCoalesc: iTabSymb[String]):
  List[CallProc] =
    procName match { //specific processing of the system calls
      case "memo" | "bug" | "show" | "copy" =>
        val l = List(this.coalesc(allCoalesc).asInstanceOf[CallProc])
        l
      case _ => val fun: DataProgLoop[_] = funs(procName) //we get the dataProgLoop
        if (fun.isLeafCaLoop) {
          //we just need to coalesc this by replacing names used either using param or using adress
          List(this.coalesc(allCoalesc).asInstanceOf[CallProc])
        }
        else {
          //we build the correspondance from formal paramter to effective
          var params: iTabSymb[String] = HashMap()
          for ((pdata, exp) <- fun.paramD zip exps) {
            val nameOp: String = exp.asInstanceOf[Read[_]].which
            params = params + (pdata -> allCoalesc.getOrElse(nameOp, nameOp)) //realizes a transitive closure, by using $assed effective parameter value?
          }
          for ((pres, name) <- fun.paramR zip names) {
            params = params + (pres -> allCoalesc.getOrElse(name, name))
          }
          fun.codeGen(heap, occupied, params) //here there are many elements in the  List.
        }

    }

  def codeGenInstrOld(heap: Vector[String], funs: iTabSymb[DataProgLoop[_]], occupied: Int, allCoalesc: iTabSymb[String]):
  List[CallProc] =
    procName match { //specific processing of the system calls
      case "memo" | "bug" | "show" | "copy" =>
        val l = List(this.coalesc(allCoalesc).asInstanceOf[CallProc])
        l
      case _ => val fun: DataProgLoop[_] = funs(procName) //we get the dataProgLoop
        if (fun.isLeafCaLoop) {
          //we just need to coalesc this by replacing names used either using param or using adress
          List(this.coalesc(allCoalesc).asInstanceOf[CallProc])
        }
        else {
          //we build the correspondance from formal paramter to effective
          var params: iTabSymb[String] = HashMap()
          for ((pdata, exp) <- fun.paramD zip exps) {
            val nameOp: String = exp.asInstanceOf[Read[_]].which
            params = params + (pdata -> nameOp)
          }
          for ((pres, name) <- fun.paramR zip names) {
            params = params + (pres -> name)
          }
          fun.codeGen(heap, occupied, params) //here there are many elements in the  List.
        }

    }

  /** substitute x in names and x in read(x) by coalesc(x) */
  override def coalesc(c: iTabSymb[String]): Instr = {
    CallProc(procName, names.map((s: String) => c.getOrElse(s, s)), exps.map(_.asInstanceOf[ASTBt[_ <: Ring]].coalesc(c)))
  }
}

/**
 *
 * @param name    variable computed
 * @param shifted input variable being shifted
 * @param perm    Compute a shift permutation.
 */
case class ShiftInstr(name: String, shifted: String, perm: Array[Int]) extends Instr {
  override def exps: List[AST[_]] = List()

  override def propagate(id1: rewriteAST2): Instr = this

  /** true for instruction part or Transfer Connected Components */
  override def isTransfer: Boolean = true

  /** names of variables modified by instruction. */
  override def usedVars(): HashSet[String] = HashSet(shifted)

  override def names: List[String] = List(name)

  /**
   *
   * @param t symbol table, to get the bitsize
   * @return a list  of Boolean Instruction compiling the integer instruction
   */
  override def unfoldInt(t: TabSymb[InfoNbit[_]]): List[Instr] = List() //we do not need it
}


/** allows to remove tm1s by storing later. */
case class Store(name: String, delay: Int, exp: AST[_]) extends Instr {
  override def toString(): String = pad(name, 25) + "Store" + delay + " " + exp.toStringTree + show(locus) + show2(locus2)

  override def exps: List[AST[_]] = List(exp)

  override def names: List[String] = List(name)

  override def propagate(id1: rewriteAST2): Instr = Store(name, delay, id1(exp))


  override def usedVars(): HashSet[String] = exp.symbolsExcepLayers

  override def unfoldInt(t: TabSymb[InfoNbit[_]]): List[Instr] = List() //we do not need it, here it is forgotten!!!!
}


/** allows to remove tm1s by storing latter. */
case class Loop(names: List[String], exps: List[AffBool]) extends Instr {
  override def toString(): String = exps.map(pad(names.reduce(_ + "," + _), 25) + _ + "\n").mkString("\n")

  override def propagate(id1: rewriteAST2): Instr = throw new Exception("not to be implemented")


  override def usedVars(): HashSet[String] = HashSet() //todo
  override def unfoldInt(t: TabSymb[InfoNbit[_]]): List[Instr] = List() //we do not need it
}

//todo on aurait pas du prendre de case class pour affect ou callProc.
case class Affect[+T](name: String, val exp: AST[T]) extends Instr {

  /* def encpasulatedConcats(s:String, e:ASTBt[UI]):ASTBt[UI]={
     var res=e
     for(i<- (1 to 5).reverse){
       val ecur: Uint = new Read[UI](s + "#" + i) with ASTBt[UI]
        res = ecur :: res
     }
      res
   }*/
  override def simplifConcat(): Instr = {
    val u=0
    def diesify(s: String) = if (s.contains('_')) s.replace('_', '#') else s + "#0" //quand c'est 0 y a pas de tiret

    exp match {
      case Call2(_, _, arg2) =>
        val res = Affect(diesify(name), arg2)
        res
      case _ => //on fait 5 calls encapsulé concat(exp,
        val res = Affect(diesify(name), exp)
        // val radName=name.dropRight(2);   val res= Affect(radName,encpasulatedConcats(radName,exp.asInstanceOf[ASTBt[UI]]))
        res
    }
  }

  def correctName(): Unit = {
    val nameE = exp.name
    if (nameE != name)
      exp.name = name
    // if (name.startsWith("ll"))    throw new Exception("ll is a reserved prefix, do not use it please")

  }


  def toStoreDetmise(): Store = {
    val e = exp.asInstanceOf[ASTBg]
    if (e.isTm1)
      Store(name, 1, e.detm1ise)
    else
      Store(name, 0, e)
  }

  override def toString: String = {
    val tabu = exp.tabulations
    " " * tabu + pad(name, 25 - tabu) + "<-  " + exp.toStringTree + show(locus) + show2(locus2)
  }

  //+(if (alignPerm.isEmpty) "" else alignPerm.map({ case (k, v) => " aligned on: " + k + " with: " + v.toList + ";  " }))

  /** Computes the max of integer length take in the input */
  def maxBitSize(t: iTabSymb[InfoNbit[_]]): Int = {
    var res: Int = 0
    for (read <- usedVars)
      res = Math.max(res, t(read).nb)
    return res
  }

  /**
   * for redop wich are also result parameters, we introduce an intermediate macroFields,
   * toto<-reduce remains  toto<-reduce  but toto is now a macrofield
   * and a suplementary affectation stores toto into totoR which is now the  paramR,
   * this manipulation will spare memory read and writes todo avoid recomputing the whole dag
   *
   * @param tSymbVar mutable symbol table will be completed
   * @return former instruction with macrofield, plus supplementary affectation
   */
  def insertMacroFieldbeforeReduceParamR(tSymbVar: TabSymb[InfoNbit[_]]): List[Instr] = {
    if (tSymbVar(name).k.isParamR && isRedop) {
      val newName = name + "R"
      tSymbVar.addOne(newName, tSymbVar(name))
      tSymbVar.addOne(name, tSymbVar(name).macroFieldise)
      val newAffect = Affect(newName, readLR(name, exp.mym.asInstanceOf[repr[(Locus, Ring)]]))
      List(this, newAffect)
    } else List(this)
  }


  def exps = List(exp)

  def isRedop = exp.asInstanceOf[ASTL.ASTLg]
    .isRedop

  val names = List(name);
  val namesDefined = List(name);


  def usedVars(): HashSet[String] = {
    // if (isShift && considerShift) HashSet(names(0).drop(5))//HashSet.empty
    if (isShift && this.isInstanceOf[Affect[_]] && !this.name.contains('$'))
      HashSet(names(0).drop(5)) //HashSet.empty
    else
    exp.symbolsExcepLayers
  }


  /** @return if instruction is ASTLt, returns the locus */
  override def locus: Option[Locus] = exp match {
    case a: ASTLt[_, _] => Some(a.locus)
    case _ => None
  }

  /** @return if instruction is ASTLt, returns the locus */
  override def ring: Option[Ring] = exp match {
    case a: ASTLt[_, _] => Some(a.ring)
    case _ => None
  }

  override def locus2: Option[Ring] = exp match {
    case a: ASTBt[_] => Some(a.ring)
    case _ => None
  }

  override def isTransfer: Boolean = exp.asInstanceOf[ASTLt[_, _]].locus.isInstanceOf[TT] // || exp.isInstanceOf[Red2[_,_,_]]
  override def propagate(id1: rewriteAST2): Instr = Affect(name, id1(exp))

  /**
   *
   * @param cs constraints for cycle
   * @param t  updated with new symbols
   * @return aligned instruction, together with shift affect
   */
  def align(cs: TabSymb[Constraint], t: TabSymb[InfoNbit[_]]): List[Instr] = {
    val r = Result()
    val newExp = exp.asInstanceOf[ASTLt[_, _]].align(r, t)
    val newAffect = Affect(name, newExp)
    newAffect.alignPerm = r.algn
    var result: List[Instr] = List()
    if (r.c != None) {
      cs.addOne(name -> r.c.get)
      result = r.si.values.toList
    }
    newAffect :: result //We return  also the shift-affect instruction
  }

  /**
   * updates alignement
   *
   * @param cs store cycle constraints
   * @param t  updated with new symbols for shift
   * @return aligned instruction, together with shift affect
   */
  def align2(cs: TabSymb[Constraint], t: TabSymb[InfoNbit[_]], alignnPerm: mutable.Map[(String, String), Array[Int]]): List[Instr] = {
    val r = Result() //collect results, r.alg contains k,v iff name is using k, and is aligned on k using v
    val newExp = exp.asInstanceOf[ASTLt[_, _]].align(r, t)
    val newAffect = Affect(name, newExp)
    newAffect.alignPerm = r.algn //to be removed
    r.algn.map({ case (k, v) => alignnPerm.addOne((name, k), v) }) //name is using k, and is aligned on k using v
    var result: List[Instr] = List()
    if (r.c != None) {
      cs.addOne(name -> r.c.get)
      result = r.si.values.toList
    }
    newAffect :: result // the shift-affect instruction is added as a new instruction
  }


  /**
   *
   * @param i   current looop index considered. -1 if boolean and not integer
   * @param gen contains all the info to produce the code
   * @param env map or scan parameter's expression for index i
   * @return The boolean affectation or boolean expression corresponding to the loop index
   */
  override def boolExprForIndexI(i: Int, gen: BitLoop, env: HashMap[String, ASTBt[B]]): ASTBt[B] = {
    exp.asInstanceOf[ASTBg].boolifyForIndexI(i, gen, gen.addSufx(name, i) /*we pass the name of the boolean variable to be affected */ , env)

  }

  /**
   *
   * @param radius contains the already computer radius
   * @param tSymbVar
   */
  override def radiusify3(radius: TabSymb[Int], tSymbVar: TabSymb[InfoNbit[_]]): Instr = {
    val (r, newExp) = exp.asInstanceOf[ASTLt[_ <: Locus, _ <: Ring]].radiusify3(radius, tSymbVar)
    radius.addOne(name -> r) //we store radius of identifier for future use.
    if (tSymbVar(name).k.isParamR)
      tSymbVar.addOne(name -> tSymbVar(name).radiusify3(r)) //for paramR, we modify the symbol table
    new Affect(name, newExp)
  }

  /*
    override def radiusify2(radius: TabSymb[Int], tSymbVar: TabSymb[InfoNbit[_]]): Unit = {
      val r: Int = exp.asInstanceOf[ASTLt[_ <: Locus, _ <: Ring]].radiusify2(radius, tSymbVar)
      radius.addOne(name -> r) //we store radius of identifier for future use.
      if (tSymbVar(name).k.isParamR)
        tSymbVar.addOne(name -> tSymbVar(name).radiusify2(r)) //for paramR, we modify the symbol table
    }


    override def radiusify(radius: TabSymb[(Int, Option[Modifier])], tSymbVar: TabSymb[InfoNbit[_]]): Unit = {
      val (r, modifier): (Int, Option[Modifier]) = exp.asInstanceOf[ASTLt[_ <: Locus, _ <: Ring]].radiusify(radius, tSymbVar)
      radius.addOne(name -> (r, modifier)) //we store radius of identifier for future use.
      if (tSymbVar(name).k.isParamR)
        tSymbVar.addOne(name -> tSymbVar(name).radiusify2(r)) //for paramR, we modify the symbol table
    }
  */

  /**
   *
   * @param t symbol table, to get the bitsize
   * @return a list  of Boolean Instruction compiling the integer instruction,
   *         also updates t adding the boolean elements of integers
   */
  override def unfoldInt(t: TabSymb[InfoNbit[_]]): List[Instr] = {
    val decall = exp.asInstanceOf[ASTBg].deCallify(HashMap.empty[String, ASTBt[B]])
    val res =
      if (decall.ring == B()) List(Affect[B](name, decall.unfoldInt(t).head))
    else {
        val boolNames = Instr.deployInt2(name, t(name)) //affectation of int has not been tested yet
      //updates t
      boolNames.map((nameb: String) => t.addOne(nameb -> new InfoNbit[B](B(), t(name).k, 1)))
      boolNames.zip(decall.asInstanceOf[ASTBt[_]].unfoldInt(t)).map(
        (namee: (String, ASTBt[B])) => Affect[B](namee._1, namee._2).asInstanceOf[Instr])
    }
    res
  }


  override def coalesc(newName: iTabSymb[String]): Affect[_] =
    Affect(if (!newName.contains(name)) name else newName(name), exp.asInstanceOf[ASTBt[_]].coalesc(newName))


  //affectation are replace by call to the copy macro, which just  copies *
  // data
  override def codeGenInstr(heap: Vector[String], funs: iTabSymb[DataProgLoop[_]], occupied: Int,
                            allCoalesc: iTabSymb[String]): List[CallProc] = {


    val res = List(CallProc("copy", List(allCoalesc.getOrElse(name, name)),
      List(exp.asInstanceOf[ASTBt[_ <: Ring]].coalesc(allCoalesc))))
    res
}
}

object CallProc {
  def apply(s: String, p: DataProg[InfoNbit[_]]): Instr = {
    val call = CallProc(s, p.paramR, p.paramD.map(x => readLR(x, repr(p.tSymbVar(x).t).asInstanceOf[repr[(_ <: Locus, _ <: Ring)]])))
    call
  }
}
object Instr {

  val isBoolean = (r: Instr) => a(r).exp.asInstanceOf[ASTBg].ring == B()

  /** used to identify system instructions show, bugif, memo... */
  val sysInstr = HashSet("ret", "bug", "sho", "mem")

  /**
   * @return true for callProc that will not need to store their result in storedField, but instead are executed directly
   *         this means in fact the "memo" callProc .memo will be replaced by affectation to paramR, when moved to macro
   **/
  def isProcessedInMacro(p: String) = p == "memo" //TODO programmer memo comme une sous classe de callProc
  //|| p.startsWith("bug") we decided to keep call to bug outside loopCA


  /**
   * @param f name of a procedure
   * @return true if f is a system call
   */
  def isSysInstr(f: String) = f.size > 2 && sysInstr.contains(f.substring(0, 3))

  /** @param i instruction
   * @return i.asInstanceOf[Affect[_]]*/
  def a(i: Instr): Affect[_] = i.asInstanceOf[Affect[_]]

  /** Generates a Read with a spatial type.*/
  def readLR(s: String, m: repr[(Locus, Ring)]) = new Read(s)(m) with ASTLt[Locus, Ring]

  /** Generates a Read with a scalar type.*/
  def readR(s: String, m: repr[Ring]) = new Read(s)(m) with ASTBt[Ring]

  def reduceR(a1: ASTBg, a2: ASTBg, opred: redop[Ring], m: repr[Ring]) =
    new Call2(opred._1, a1, a2)(m) with ASTBt[Ring]


  /** utility used to align instruction when printed */
  def pad(s: String, n: Int): String = s + " " * (n - s.length())

  //  def apply(s: String, p: ProgData2): Instr = CallProc(s, p.paramR,
  //    p.paramD.map(x => read(x, repr(p.tSymbVar(x).t).asInstanceOf[repr[(_ <: Locus, _ <: Ring)]])))

  /*/**
   * @param s name of function
   * @param p the function itself
   * @return call to that function. effective parameter's name, are identical to formal.
   */
  def apply(s: String, p: DataProg[InfoNbit[_]]): Instr = {
    val call = CallProc(s, p.paramR, p.paramD.map(x => readLR(x, repr(p.tSymbVar(x).t).asInstanceOf[repr[(_ <: Locus, _ <: Ring)]])))
    call
  }*/

  /**
   *
   * @param n identifier
   * @param tSymb
   * @return add one (resp. two) suffixes to the variable names, for simplicial (resp. tranfer) variable
   */
  private def deploy(n: String, tSymb: TabSymb[InfoNbit[_]]): List[String] =
    Locus.deploy(n, tSymb(n).t.asInstanceOf[(_ <: Locus, _)] _1)

  private var nameCompteuraux = 0

  def getCompteurAux: Int = {
    nameCompteuraux += 1;
    nameCompteuraux
  }


  private def newAux(): String = "_aux" + getCompteurAux

  /**
   *
   * @param tsymb
   * @param paramRmut side effect: will receive the name of the result parameters, in right order
   * @param e         the expression returned incuding possibly Coons, to gather several parameters.
   * @return Affect Instructions which affect values computed by the function, to resultParameters.
   */
  def affectizeReturn(tsymb: TabSymb[InfoType[_]], paramRmut: mutable.LinkedHashSet[String], e: AST[_]): List[Instr] = {
    /**
     * @param e of the form Coons(e1,e2)
     * @return Affect of value computed by the function, to resultParameters.
     */
    def process(e: AST[_]): List[Affect[_]] = {
      val already = tsymb.contains(e.name)
      val newName = if (e.name != null && (!already || (already &&
        (tsymb(e.name).k == MacroField() || tsymb(e.name).k == StoredField()))
        )) e.name else "resultCA"
      //we create another variable to return result, in case it is a layer.
      paramRmut += newName;
      tsymb += newName -> InfoType(e, ParamR())
      if (already && newName == e.name) List() else List(Affect(newName, e))
    }
    //recursive call because a function can returns several results grouped  together using Coons()
    e match {
      case Cons(e1, e2) => process(e1) ::: affectizeReturn(tsymb, paramRmut, e2)
      case _ => process(e)
    }
  }

  /**
   *
   * @param n  name of integer parameter
   * @param nb number of bits of integer
   * @return list of names, one for each bit, obtained by appending the bit index.
   *         if name was already a boolean, nothing is changed.
   */
  def deployInt2(n: String, i: InfoNbit[_]): List[String] = {
    if (i.t == B() || (i.t.isInstanceOf[Tuple2[_, _]] && i.ring == B()))
      List(n)
    else
      (0 to i.nb - 1).map(n + "#" + _).toList
  } //if nb=1, and locus is Int, we will still generate a deploy
}



