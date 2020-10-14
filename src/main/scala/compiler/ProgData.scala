package compiler

import compiler.AST._
import compiler.ASTB._
import compiler.ASTBfun.ASTBg
import compiler.Dag._
import compiler.ProgData._
import compiler.VarKind._

import scala.collection._
import scala.collection.immutable.HashMap
import scala.language.postfixOps
/**The most elementary info stored in symbol table: type and kind */
class InfoType[+T](val t: T, val k: VarKind) { override def toString: String = t.toString + " " + k.toString }

object InfoType {
  def apply(e: AST[_], k: VarKind): InfoType[_] = new InfoType(e.mym.name, k)
  def addSymb(t: TabSymb[InfoType[_]], e: AST[_], k: VarKind): t.type = t += e.name -> InfoType(e, k)
  def addSymbL(t: TabSymb[InfoType[_]], e: AST[_], k: VarKind): t.type = t += "l" + e.name -> InfoType(e, k)
}

/** info stored in symbol table, after computing nbit: type and kind and nbit */
class InfoNbit[+T](override val t: T, override val k: VarKind, val nb: Int) extends InfoType(t, k) {
  val u = 2; override def toString: String = t.toString + " " + k.toString + " " + nb
}

object ProgData {
  private var nameCompteur = 0

  def getCompteur: Int = { nameCompteur += 1; nameCompteur }
  def newFunName(): String = "_fun" + getCompteur

  def string(l: List[_], c: String): String = l.foldLeft("")(_ + c + _)
  def listOf[T](t: Map[String, T]): List[(String, T)] = { val (anon, definedMacros) = t.partition((x: (String, T)) => x._1.startsWith("_fun")); anon.toList ::: definedMacros.toList }
  // def string(t: iTabSymb[_], c: String): String = t.map { case (k, v) ⇒ k → v.toString }.foldLeft(" ")(_ + c + _)
  /**pring a map on several small lines, instead of one big line */
 // def string[T](t: TabSymb[T], s: String): String = t.toList.grouped(4).toList.map(_.mkString(s)).mkString("\n") + "\n"
  def string[T](t: TabSymb[T], s: String): String = t.toList.grouped(4).map(_.mkString(s)).mkString("\n") + "\n"

  /**add one (resp. two) suffixes to the variable names, for simplicial (resp. tranfer) variable */
  def deploy(n: String, tSymb: TabSymb[InfoNbit[_]]): List[String] = deploy(n, tSymb(n).t.asInstanceOf[(_ <: Locus, _)]_1)
  def deploy(n: String, l: Locus): List[String] = l match {
    case s: S      => s.sufx.map(n + "$" + _).toList
    case T(s1, _) => s1.sufx.map((suf1: String) => l.sufx.map(n + "$" + suf1 + _).toList).toList.flatten
  }

  //=> s1.sufixeS.map(s:String=>

  type TabSymb[T] = mutable.HashMap[String, T]; type AstField[T] = mutable.HashMap[AST[_], T]
  type TabConstr = TabSymb[ Constraint]
  type iTabSymb[T] = Map[String, T];
  type iTabSymb2[T] = immutable.HashMap[String, T];

  type iAstField[T] = Map[AST[_], T]
  /**spatial unfolding of an ASTL of "simplicial" type creates an array of array of ASTB. The cardinal of first array is 1,2,3 for V,F,E,  */
  type ArrAst = Array[ASTBg]
  /**spatial unfolding of an ASTL of "transfer type" creates an array of array of ASTB. The cardinal of first array is 1,2,3 for V,F,E, the seconds array is 6,3,2  */
  type ArrArrAst = Array[Array[ASTBg]]
  /**
   * The only place where a machine differs from another is when compiling the transfer function,
   * it is parameterise by One function for each pair of simplicial type.
   * Type of input is transfer(src,des) type of output is transfer(des,src) , where "src" is first S, and "des" is second S
   */
  type Machine = (S, S, ArrArrAst) => ArrArrAst

  /**
   * The hexagon machine models communication according to the perfect hexagonal grid.
   * diagonal (d1,d2) and antidiagonla (ad1,ad2) are oriented so that all the shift and delay gets applied on d1 (up), so that the same computation is applied
   * on d2 and ad2, when the vE fields is obtain by a broadcast followed by a transfer.
   */

  val hexagon: Machine = (src: S, des: S, t: ArrArrAst) => {
    implicit val scalarType: repr[_ <: Ring] = t(0)(0).mym; src match {
      case V() => des match {
        case E() => /*eV->vE*/
          val Array(e, ne, nw, w, sw, se) = t(0)
          Array(Array(shiftL(Tminus1(w)), Tminus1(e)), Array(Tminus1(se), nw), Array(shiftL(Tminus1(sw)), ne))
        case F() => /*fV->vF*/
          val Array(ne, n, nw, sw, s, se) = t(0); Array(Array(n, Tminus1(sw), Tminus1(se)), Array(shiftL(Tminus1(s)), ne, shiftL(nw)))
      }
      case E() =>
        val Array(Array(h1, h2), Array(d1, d2), Array(ad1, ad2)) = t; //common to vE and fE
        des match {
          case V() => /*vE->eV*/
            Array(Array(h2, Tminus1(ad2), Tminus1(shiftR(d2)), shiftR(h1), shiftR(ad1), d1))
          case F() => /*fE->eF*/
            Array(Array(Tminus1(h2), Tminus1(ad1), Tminus1(d1)), Array( h1   ,Tminus1(shiftL(ad2)) , Tminus1(d2)))
        }
      case F() => des match {
        case V() => /*vF->fV*/
          val Array(Array(dp, db1, db2), Array(up, ub1, ub2)) = t; Array(Array(Tminus1(shiftR(ub1)), Tminus1(dp),  Tminus1(shiftR(ub2))), Array(  shiftR(db1) ,shiftR(up),  db2) )
        case E() => /*eF->fE*/
          val Array(Array(db, ds1, ds2), Array(ub, us1, us2)) = t; Array(Array(Tminus1(ub), db), Array(ds2, us2), Array(ds1, shiftR(us1)))
      }
    }
  }
  /** correspondance between suffix and index */
  val order: HashMap[String, Int] = immutable.HashMap("w" -> 0, "nw" -> 1, "ne" -> 2, "e" -> 3, "se" -> 4, "sw" -> 5,
    "wn" -> 0, "n" -> 1, "en" -> 2, "es" -> 3, "s" -> 4, "ws" -> 5,
    "h" -> 0, "d" -> 1, "ad" -> 2,
    "h1" -> 0, "h2" -> 1, "d1" -> 2, "d2" -> 3, "ad1" -> 4, "ad2" -> 5,
    "do" -> 0, "up" -> 1,
    "dop" -> 0, "dob1" -> 1, "dob2" -> 2, "upp" -> 3, "upb1" -> 4, "upb2" -> 5,
    "dob" -> 0, "dos1" -> 1, "dos2" -> 2, "upb" -> 3, "ups1" -> 4, "ups2" -> 5)
  val transfers: List[(S, S)] = List((V(), E()), (E(), V()), (V(), F()), (F(), V()), (E(), F()), (F(), E()))

  /** generates an input array*/
  def inAr(s1: S, s2: S): ArrArrAst = { var i = -1; def nameInt = { i += 1; "" + i }; def myp() = new Param[B](nameInt) with ASTBt[B]; Array.fill(s1.arity)(Array.fill(6 / s1.arity)(myp())) }
  /** automatically computes permutation implied by hexagon*/
  val hexPermut: immutable.Map[(S, S), Array[Int]] = immutable.HashMap.empty ++ transfers.map((ss: (S, S)) => ss ->
    {
      val (s1, s2) = ss; val t = hexagon(s1, s2, inAr(s1, s2)); val l = t.map(_.toList).toList.flatten; //compute the permutation of T[S1,S2] => T[S2,S1]
      val r = new Array[Int](6); var i = 0; for (a <- l) { r(i) = a.symbols.head.toInt; i += 1 }; r
    })
  
  def apply[T](f: Fundef[T], repl: iAstField[AST[_]] = immutable.HashMap.empty): ProgData[_] = {
    val (computeNodes, _) = getGreater(
      f.body :: repl.values.toList,
      immutable.HashSet.empty[AST[_]] ++ repl.keys) //those are passed so as not to be visited.
    val allNodes = computeNodes ::: repl.keys.toList //the keys have not been visited, so we must explicitely add them into all nodes.
    Name.setName(f, ""); //for ''grad'' to appear as a name, it should be a field of an object extending the fundef.
    val funs: iTabSymb[Fundef[_]] = immutable.HashMap.empty ++ computeNodes.collect { case l: Call[_] => (l.f.namef, l.f) }
    new ProgData[T](f, funs.map { case (k, v) ⇒ k -> ProgData(v) }, allNodes)
  }

}

/**
 * Retrieves all the compute nodes associated to a function
 *
 * @param f the function,
 * @param funs functions decomposing the code in a modular way
 * @param allNodes all the AST nodes.
 */
//noinspection ScalaUnnecessaryParentheses,ScalaUnnecessaryParentheses,ScalaUnnecessaryParentheses,ScalaUnnecessaryParentheses
class ProgData[+T](val f: Fundef[T], val funs: iTabSymb[ProgData[_]], val allNodes: List[AST[_]]) {

  /**
   * Replaces DAG by a list of trees, adding a read node using names, and building  a list  of affect instruction.
   *  also does Substitution which is usefull only for the main body, the
   *     @param replaced   substitution map
   */
  def deDagise(replaced: iAstField[AST[_]] = immutable.HashMap.empty): ProgData1[T] = {
    val instrs = allNodes.flatMap(_.sysInstrs)
    val represent = immutable.HashMap.empty[AST[_], AST[_]] ++ allNodes.map(x => x -> x) //necessary because distinct AST can be equals  when compared as case class hierarchie
    val invertReplaced = replaced.map { _.swap }; //whenever the value is used, we need to count 1 for the key, so we compute the invertReplace map
    val users = f.body :: instrs.map(_.exp) //instruction using exp needs to be considered as users of exp also
    val nUser = immutable.HashMap.empty[AST[_], Int] ++ (allNodes.flatMap(_.inputNeighbors) ++ users).map(l => invertReplaced.getOrElse(l, l))
      .groupBy(identity).map { case (k, v) ⇒ k -> v.size }
    val usedTwice = allNodes.filter(e => nUser.contains(e) && nUser(e) > 1)
    // for (e <- usedTwice /**  ++ allNodes*/ ) e.checkName() //donne un nom. -- TODO verify if we should really name all the nodes, its better to name only the reused expression to avoid generating big numbers for aux.

    val usedTwiceAsValue = usedTwice.map(e => replaced.getOrElse(e, e)) //among the ast being reused, if one is among those to be substituted, then it is substituted.
    val UsedTwiceAskey = usedTwiceAsValue.filter(t => invertReplaced.contains(t)).map(e => invertReplaced(e))

    //  val needAffect: immutable.HashSet[AST[_]] = immutable.HashSet.empty ++ allNodes.filter { e => //we force affectation on those to facilitate latter processing @TODO forcer aussi l'affect sur les parametres données.
    //    e match { case Taail(_) | Heead(_) | Call1(_, _) | Call2(_, _, _) | Call3(_, _, _, _) => !usedTwiceAsValue.contains(e) case _ => false }    }
    val redops=immutable.HashSet.empty ++ allNodes.flatMap { _.redExpr }
    val callAndHeadAndRedop = allNodes.filter((x: AST[_]) =>
      if(redops.contains(x)) true    else
        x match {
      case Taail(_) | Heead(_) | Call1(_, _) | Call2(_, _, _) | Call3(_, _, _, _) => true
      case a: ASTL[_, _] => a.shouldAffect
      case ast:AST[_]=> redops.contains(ast)
    })
    val inCall = callAndHeadAndRedop.flatMap(_ match { case c: Call[_] => c.args.filter(_.inputNeighbors.nonEmpty).toList case _ => List[AST[_]]() })
    val needAffect2 = callAndHeadAndRedop ::: inCall //.filter(  !usedTwiceAsValue.contains(_))
    //  for (e <- needAffect2   ) e.checkName()
    val affectExpList2 = immutable.HashSet.empty[AST[_]] ++ usedTwiceAsValue ++ needAffect2
    val affectExpList2ordered = allNodes.filter(affectExpList2.contains) //exploits the fact that allNodes are naturally topologically ordered to peserve the order for the list of affectations.
    for (e <- affectExpList2ordered) e.checkName()
    if ((immutable.HashSet.empty ++ affectExpList2ordered.map(_.name)).size < affectExpList2ordered.size) throw new RuntimeException("a name is reused two times") //since name are given by hand we check that no two names are equals
    for ((k, v) <- replaced) represent(v).setName(k.name) //the name of the key (to be replaced) is transfered to the replacing value.
    val toBeReplaced = affectExpList2 ++ UsedTwiceAskey
    val affectExpList = affectExpList2ordered.map(e => e.deDag(toBeReplaced - e, represent, replaced)).reverse //we remove e from usedTwice to avoid generate e=read(e) !!!!
    val t: TabSymb[InfoType[_]] = mutable.HashMap.empty
    t ++= affectExpList.map(e => (e.name, new InfoType(e.mym.name.asInstanceOf[T], Field())))
    t ++= f.p.toList.map(a => ("p" + a.name, InfoType(a, ParamD()))) //type of parameters this statement must happen after the addition of affects otherwise paramD varkind will be replaced by Affectk
   // affectExpList.map(e=>println(e.name + "="+ e.toStringTree))

    val affectInstr = affectExpList.map(e => Affect(e.name, e))
    val allUsedTwice = immutable.HashSet.empty[AST[_]] ++ usedTwiceAsValue ++ UsedTwiceAskey

    val newInstrsSys = allNodes.flatMap(e => {
      e.sysInstrs.map(i => new UsrInstr(i.c, i.exp.deDag(toBeReplaced, represent, replaced)) //  dedagify   exp used in system instructions
        .affectize(e, allUsedTwice.contains(i.exp), t))
    }).flatten //one flatten for list of list, and another one for None/Some
  //  print(string(t , "  | "))
    f.body = f.body.deDag(toBeReplaced, represent, replaced)
    new ProgData1(f, affectInstr ::: newInstrsSys.reverse, funs.map { case (k, v) ⇒ k -> v.deDagise() }, t, f.p.toList.map("p" + _.name), List()) //result parameter to be added letter by procedure step.
  }
}

/**
 * Stores all the data associated to a program, used for compilation
 *  @ tSymbVar,  stores info about parameters or re-used expression,
 * @ Info: Type associated to variable, number of bits, to be completed progressively.
 * @ instrs instructions of the program (return, display, debug,...), the return instruction is stored separately.
 * @ funs list of functions used by the program, indexed by names.
 * * @ signature, list of parameters, Information of results.
 */

class ProgData1[+T](val f: Fundef[T], val instrs: List[Instr], val funs: iTabSymb[ProgData1[_]], val tSymbVar: TabSymb[InfoType[_]],
                    val paramD: List[String], val paramR: List[String]) {
  override def toString: String = paramD.mkString(" ") + "=>" + paramR.mkString(" ") + "\n" + instrs.mkString("") +
    string(tSymbVar, "  | ") + "\n" + listOf(funs).mkString("\n \n  ")

  // override def toString: String = string(paramD, " ") + "=>" + string(paramR, " ") + "\n" + string(instrs, " ") + "\n" + tSymbVar.toString + "\n" + string(funs, "\n Macro:") + "\n"
  /**replaces function call by procedure call, introduces new names in tabSymb*/
  def procedurise(): ProgData1[T] = {
    val procedureFun = funs.map { case (k, v) => k -> v.procedurise() }
    val hd: TabSymb[String] = mutable.HashMap.empty; val tl: TabSymb[String] = mutable.HashMap.empty
    val paramRmut = mutable.LinkedHashSet.empty[String] //we use LinkedHashSet as opposed to Hashset, to preserve the order of insertion because order of parameter is informational
    for (i <- instrs) i.buildhdtl(hd, tl)
    val paraResAffect = Instr.affectizeReturn(tSymbVar, paramRmut, f.body).flatMap(_.procedurise(hd, tl, tSymbVar))
    new ProgData1(f, instrs.flatMap(i => i.procedurise(hd, tl, tSymbVar)) ::: paraResAffect, procedureFun, tSymbVar, paramD, paramRmut.toList)
  }
  /**
   * Computes the number of bits of parameters, and affectation, and also internal nodes of all the ASTs.
   *   @param nbitP: list of number of bits for each parameter assumed to be ASTLs.
   */
  def nbit(nbitP: List[Int]): ProgData2 = {
    val nbitExp: AstField[Int] = mutable.HashMap.empty
    val newFuns: TabSymb[ProgData2] = mutable.HashMap.empty
    val newtSymb: TabSymb[InfoNbit[_]] = mutable.HashMap.empty //we store the number of bits of parameters in newTabSymbVar:
    //Initalize the nbit of layers
    tSymbVar.map { case (nom, v) => if (v.k.isLayer) newtSymb += nom -> new InfoNbit(tSymbVar(nom).t, tSymbVar(nom).k, v.k.asInstanceOf[LayerField].nb) }

    newtSymb ++= (paramD zip nbitP).map { case (nom, nbi) => nom -> new InfoNbit(tSymbVar(nom).t, tSymbVar(nom).k, nbi) } //we assume that parameter are ASTLs
    val newInstrs = instrs.map(_.nbit(this, nbitExp, newtSymb, newFuns))
    new ProgData2(newInstrs, newFuns, newtSymb, paramD, paramR)
  }

}

    //  a.exp.isInstanceOf[Layer[_,_]] 