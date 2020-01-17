package compiler

import compiler.AST._
import compiler.ProgData._

import scala.collection._

/**
 * Analysed by the compiler to produce a CA rule, a circuit is implemented like a function definition:
 *  parameter corresponds to external generated fields input to  the CA
 *  they must be present in the memory, before the main loop is called.
 * return results are fields produced by the CA, to be used by an host.
 * they are in the memory after the main loop is called.
 * Normally, it is the caller which decides where the result of the main are stored,
 * however, for the main, we can suppose the offset of Data Param starts at Zero.
 * the main's signature and those compiled offset must be accessible from the host.
 * We imagine that another compiler towards 1D can be used to do the interface: produce the 2D input and read the 2D output, on the border
 * both 1D and 2D compilation can be linked, as far as offset computation goes.
 * In turns, the 1D CA takes input output fields produced by the host, on a single cell (or on four corners)
 */
abstract class Circuit[L <: Locus, R <: Ring](override val p: Param[_]*) extends AST.Fundef[(L, R)]("main", null, p: _*) {
  /** to be defined in the circuit for collecting all the nodes participating in usefull computation,   "abstract def" because known latter*/
  def computeRoot: ASTLt[L, R]

  /**
   * Compiles the circuit
   *  Algorithm of compilation generates big maps used temporarily such as usedmorethanonce, to update a state.
   *  after generating the instruction,  the state is contained in  three  maps: allinstructions,  affectmap, fundef
   *  after computing nbit, we then have 1-a table which tells how much bits are used for each symbol
   *                                     2-a table  which tells for each expression, how much bits is needed to store them.
   *  @replaced contains substitution pair, the left hand side, is replaced by the right hand side
   */

  def compile(m:Machine, replaced: List[(AST[_], AST[_])] = List()): Unit = {
    body = computeRoot //we pretend that the circuit is a function.
    val repl: iAstField[AST[_]] = immutable.HashMap.empty ++ replaced.toMap
    val prog1 = ProgData(this, repl)
    val prog2 = prog1.deDagise(repl); // print(prog2);
    val prog3 = prog2.procedurise()
    val prog4 = prog3.nbit(List(1)); //faut mettre les tailles des entiers utilisés pour appeller main.
    val prog5=prog4.macroise()
    print(prog5+ "\n\n")
    val prog6=prog5.unfoldSpace(m)
      print(prog6);  
    val prog7=prog6.foldRegister()
    //TODO mettre les noms sur les fonctions, aussi.
  }
}
 
