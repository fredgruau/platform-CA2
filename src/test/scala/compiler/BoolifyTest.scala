package compiler

import compiler.AST.{Call1, Call2, Call3, Param, Read}
import compiler.ASTB.{AffBool, And, False, Mapp1, Mapp2, Neg, Or, True, Xor, toBinary}
import compiler.ASTBfun._
import compiler.Circuit.{TabSymb, iTabSymb}
import compiler.VarKind.MacroField
import dataStruc.DagInstr
import org.scalatest.FunSuite

import scala.collection.immutable.HashMap
import scala.collection.mutable

/** Test the correct implementation of unfoldInt, */
class BoolifyTest extends FunSuite {

  /**
   *
   * @param code one line of code
   * @param env  stores the modification of boolean variables, resulting from executing the code
   * @return final environement containing the result
   */
  private def eval(code: ASTBt[B], env: HashMap[String, Boolean]): (HashMap[String, Boolean], Boolean) = {
    code.asInstanceOf[AST[B]] match {
      case Read(s) =>
        (env, env(s))
      case _ => code.asInstanceOf[ASTB[B]] match {
        case AffBool(nameb: String, arg: ASTBt[B]) => {
          val (newEnv, value) = eval(arg, env);
          (newEnv + (nameb -> value), value)
        }
        case Or(x, y) => {
          val (env1, val1) = eval(y, env); val (env2, val2) = eval(x, env1); (env2, val1 || val2)
        }
        case And(x, y) => {
          val (env1, val1) = eval(y, env); val (env2, val2) = eval(x, env1); (env2, val1 && val2)
        }
        case Xor(x, y) => {
          val (env1, val1) = eval(y, env); val (env2, val2) = eval(x, env1); (env2, val1 != val2)
        }
        case Neg(x) => {
          val (env1, val1) = eval(x, env); (env1, !val1)
        }
        case True() => (env, true)
        case False() => (env, true)
      }
    }
  }

  /**
   *
   * @param codeLines several line of code
   * @param env       stores the modification of boolean variables, resulting from executing the code
   * @return final environement containing the result
   */
  private def evalLines(codeLines: List[ASTBt[B]], env: HashMap[String, Boolean]): HashMap[String, Boolean] = {
    var envCur = env
    var b: Boolean = true
    for (lineCode: ASTBt[B] <- codeLines) {
      envCur = eval(lineCode, envCur)._1
    }
    envCur
  }

  /**
   *
   * @param env      former environment
   * @param name     of variable whose value should be added in the environment
   * @param value1   integer value
   * @param tSymbVar to find out the type, the number of bits of variables
   * @return new environement with several boolean defining the integer variable
   */
  def add(env: HashMap[String, Boolean], name: String, value1: Int, tSymbVar: TabSymb[InfoNbit[_]]): HashMap[String, Boolean] = {
    val info = tSymbVar(name)
    val booleans = ASTB.toBinary(value1, info.nb)
    var e = env
    for (i <- 0 to info.nb - 1)
      e = e + ((name + "#" + i) -> booleans(i))
    e
  }

  /**
   *
   * @param env      former environment
   * @param name     of variable whose value should be retrieved from the environment
   * @param tSymbVar to find out the type, the number of bits of variables
   * @return integer value of the variable called "name"
   */
  def get(env: HashMap[String, Boolean], name: String, tSymbVar: TabSymb[InfoNbit[_]]): Int = {
    val info = tSymbVar(name)
    var res = 0
    for (i <- info.nb - 1 to 0 by -1)
      res = 2 * res + (if (env(name + "#" + i)) 1 else 0)
    res
  }

  /**
   * evaluate the effect of an affectation on some input variables of a given type
   *
   * @param inputVar name and integer value of input variables
   * @param info     type of variables (signed or unsigned) number of bits
   * @param aff      target affectation whose compilation should be verified
   */
  def evalCode(inputVar: List[(String, Int)], info: InfoNbit[_], aff: Affect[_]): Int = {
    val tSymbVar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    var env: HashMap[String, Boolean] = HashMap()
    for ((v, int) <- inputVar) {
      tSymbVar.addOne(v -> info)
      env = add(env, v, int, tSymbVar)
    }
    tSymbVar.addOne(aff.name -> info)
    val dag: DagInstr = DagInstr(List(aff))
    val dataProg = new DataProg(dag, HashMap(), tSymbVar, List(), List(), HashMap()).loopIfy().unfoldInt()
    println(dataProg)
    env = evalLines(dataProg.totalCode, env)
    get(env, aff.name, tSymbVar)
  }

  val SI4 = new InfoNbit(SI(), MacroField(), 4)
  val b: ASTBt[SI] = new Read("b")(repr.nomSI) with ASTBt[SI]
  val c: ASTBt[SI] = new Read("c")(repr.nomSI) with ASTBt[SI]

  test("incSI") {
    val testInc = Affect("a", new Call1(incSI.asInstanceOf[Fundef1R[SI]], b) with ASTBt[SI])
    assert(evalCode(List(("b", 5)), SI4, testInc) == 6)
  }
  test("addSI") {
    val testAdd = Affect("a", new Call2(ASTBfun.add[SI].asInstanceOf[Fundef2R[SI]], b, c) with ASTBt[SI])
    assert(evalCode(List(("b", 5), ("c", 2)), SI4, testAdd) == 7)
  }
  test("minSI") {
    val testMin = Affect("a", new Call2(minRelSI.asInstanceOf[Fundef2R[SI]], b, c) with ASTBt[SI])
    assert(evalCode(List(("b", 5), ("c", 2)), SI4, testMin) == 2)
  }

}