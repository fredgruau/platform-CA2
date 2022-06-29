package compiler

import AST.{Call1, Call2, Call3, Delayed, Fundef1, Fundef2, Fundef3, Layer, Param, Read, AstPred}
import ASTB.{And, Dir, Extend, False, Intof, Mapp2, Or, ParOp, Scan1, Scan2, Tminus1, True, Xor, nbitCte, rewriteASTBt}
import ASTBfun.{ASTBg, Fundef2R}
import ASTL.rewriteASTLt
import Circuit.{TabSymb, iTabSymb, iTabSymb2}

import scala.collection.{Map, immutable, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import Array._
import ASTB._
import dataStruc.Named

/** Identifies AST corresponding to int or bool, excludes those obtained with cons */
trait ASTBt[+R <: Ring] extends AST[R] with MyOpB[R] with MyOpIntB[R] {
  self: AST[R] =>
  def isConst = false


  /** return the affbool that label subtrees neares to the root */
  def affBoolify(): List[ASTBt[B]] = {
    inputNeighbors.flatMap(_.asInstanceOf[ASTBt[_]].affBoolify())
  }

  def codeGen(i: Int, gen: CodeGen, name: String, env: HashMap[String, ASTBt[B]]): ASTBt[B] = {
    val exp = this.asInstanceOf[AST[_]] match {
      case u@Param(_) => env(u.nameP)
      case Read(x) =>
        if (gen.tablePipelined.contains(x)) {
          if (gen.evaluated(x) * gen.step > i * gen.step)
            throw new Exception("when a map is combined with a scan with initused, the scan must comes first for pipelining to work!!")
          //with initused, it is the map which will first read the pipelined array, the scan will not.
          if (gen.evaluated(x) * gen.step < i * gen.step) { //means that we have not yet compiled x's pipelined expression
            gen.evaluated += (x -> i) //register the fact that yes now we 'll compile it
            val newExp = gen.tablePipelined(x).exps(0).asInstanceOf[ASTBg].codeGen(i, gen, null, env) //compiles it
            val s: String = if (gen.lastIter(i) && gen.pipeUs(x) == 1) null else x //for last iteration, a pipelined variable used once need not be stored,
            affBoolConst(s, newExp, gen)
          }
          else
            gen.readWithConst(x)
        }
        else {
          assert(gen.tSymbVar.contains(x) || Named.isTmp(x) ||
            gen.tSymbVar.contains(gen.coalescSafe(x)), "could not find" + x) //x has to be a register generated during spatial unfolding
          //it could also be a temporary arithmetic variable generated for a previous loop
          gen.readWithConst(gen.addSufx(x, i))
          //new Read(x+sufx)(repr(B())) with ASTBt[ B ]
        }
    }
    affBoolConst(name, exp, gen)
  }


  def ring: R = mym.name


  def detm1iseR: ASTBg = {
    this.asInstanceOf[AST[_]] match {
      case Read(_) => this
      case Call1(f, a) => new Call1(f.asInstanceOf[Fundef1[Any, R]], a.asInstanceOf[ASTBt[_]].detm1iseR)(mym) with ASTBt[R]
      case Call2(f, a, a2) => new Call2(f.asInstanceOf[Fundef2[Any, Any, R]],
        a.asInstanceOf[ASTBt[R]].detm1iseR,
        a2.asInstanceOf[ASTBt[R]].detm1iseR)(mym) with ASTBt[R]
      case _ =>
        throw new Exception("on devrait traiter ca la ")

    }
  }

  /** remove the head tm1 */
  def detm1ise: ASTBt[R] = this

  /** sinon y a une erreur du compilo scala empty modifier. */
  val u = 3;
  val v = 3
  /*

    def unfoldBit(env: HashMap[String, List[ASTBt[B]]],tabSymb:  TabSymb[InfoNbit[_]]): List[ASTBt[B]]=
      this.asInstanceOf[AST[_]] match  {
        case Read(x) =>range(0,tabSymb(x).nb).toList.map( (i:Int)=>(new Read[B](x+i)(new repr[B](B())) with ASTBt[B]).asInstanceOf[ASTBt[B]] )
        case u @ Param(_)            => env(u.nameP)
        case Call1(op, x)         =>
          val newEnv= env + (op.p1.nameP -> x.asInstanceOf[ASTBg].unfoldBit(env,tabSymb))
          op.arg.asInstanceOf[ASTBg].unfoldBit(newEnv ,tabSymb)
        case Call2(op, x, y)         =>
          val newEnv= env + (op.p1.nameP -> x.asInstanceOf[ASTBg].unfoldBit(env,tabSymb))+
            (op.p2.nameP  -> y.asInstanceOf[ASTBg].unfoldBit(env,tabSymb))
          op.arg.asInstanceOf[ASTBg].unfoldBit(newEnv ,tabSymb)
      }
  */


  /** return the direction if there is one */
  def dir1: Option[Dir] = if (isInstanceOf[ParOp[_]]) Some(asInstanceOf[ParOp[_]].dirNarrowed)
  else if (isInstanceOf[Read[_]]) Some(Both())
  else None

  /**
   *
   * @param env     used to store parameter's value
   * @param tabSymb stores scalar variable that had to be introduced. in fact we need only count them and take the max for all integer affectation
   * @return we evaluate all the calls and only the calls,
   *         that produces a big pure ASTL tree and gives an idea of what is there.
   **/
  def deCallify(env: HashMap[String, ASTBg], tabSymb: TabSymb[InfoNbit[_]]): ASTBg =
    this.asInstanceOf[AST[_]] match {
      case Read(x) =>
        this.asInstanceOf[ASTBt[B]]
      case u@Param(_) => env(u.nameP) //soit un read soit un readscalar soit un affectscalar suivant la nature du parametre
      case Call1(op, x) => //il se peut quon rajute un affect et augmente la tsymb au lieu d' augmenter l'environnement
        //we check that x 's type is a subtype of the paramater
        // we dlike to write something like that op.p1.mym=x.mym
        if (x.mym.name != op.p1.mym.name)
          throw new Exception("Faut preserver SI ou UI")
        val newEnv = env + (op.p1.nameP -> x.asInstanceOf[ASTBg].deCallify(env, tabSymb))
        op.arg.asInstanceOf[ASTBg].deCallify(newEnv, tabSymb)
      case Call2(op, x, y) => //il se peut quon rajute un affect et augmente la tsymb
        if (x.mym.name != op.p1.mym.name || y.mym.name != op.p2.mym.name)
          throw new Exception("Faut preserver SI ou UI")
        val newEnv = env + (op.p1.nameP -> x.asInstanceOf[ASTBg].deCallify(env, tabSymb)) +
          (op.p2.nameP -> y.asInstanceOf[ASTBg].deCallify(env, tabSymb))
        op.arg.asInstanceOf[ASTBg].deCallify(newEnv, tabSymb)
      case Call3(op, x, y, z) => //il se peut quon rajoute un affect et augmente la tsymb
        val newEnv = env +
          (op.p1.nameP -> x.asInstanceOf[ASTBg].deCallify(env, tabSymb)) +
          (op.p2.nameP -> y.asInstanceOf[ASTBg].deCallify(env, tabSymb)) +
          (op.p3.nameP -> z.asInstanceOf[ASTBg].deCallify(env, tabSymb))
        op.arg.asInstanceOf[ASTBg].deCallify(newEnv, tabSymb)
    }

  /**
   *
   * @param newName correspondance towards scalar names
   * @return same tree except target is replaced by src   */

  def coalesc(newName: iTabSymb[String]): ASTBt[R] = {
    val rewrite: rewriteASTBt[R] = (d: ASTBt[R]) => d.coalesc(newName)
    val newD: ASTBt[R] = this match {
      case a: ASTB[R] => a.asInstanceOf[ASTB[_]] match {
        case AffBool(x, exp) => AffBool(newName.getOrElse(x, x), exp.coalesc(newName)).asInstanceOf[ASTBt[R]]
        case _ => a.propagateASTB(rewrite)
      }

      case _ => this.asInstanceOf[AST[_]] match {
        case Read(x) =>
          if (!newName.contains(x)) this
          else new Read[R](newName(x))(mym) with ASTBt[R]
        //the copy calls done by AST'propagate will preserve the trait ASTBt[R]===>NOT
        case Call1(f, a) => new Call1(f.asInstanceOf[Fundef1[Any, R]], a.asInstanceOf[ASTBt[_]].coalesc(newName))(mym) with ASTBt[R]
        case Call2(f, a, a2) => new Call2(f.asInstanceOf[Fundef2[Any, Any, R]],
          a.asInstanceOf[ASTBt[R]].coalesc(newName),
          a2.asInstanceOf[ASTBt[R]].coalesc(newName))(mym) with ASTBt[R]

        // case _ => (this.propagate((d: AST[R]) => d.asInstanceOf[ASTBt[R]].coalesc(newName).asInstanceOf[AST[R]])).asInstanceOf[ASTBt[R]]
      }
    }
    newD.asInstanceOf[ASTBt[R]]
  }

  /**
   * Important to specify that the L,R type of AST nodes is preserved, for type checking consistency
   * Surprisingly, when building ASTL explicitely, we need to drop the fact that the type is preserved,
   * and go from ASTL[L,R] to ASTLg
   * Transform a Dag of AST into a forest of trees, removes the delayed.
   *
   * @return the Dag where expression used more than once are replaced by read.
   *         generates ASTs such as READ that preserve the implementation of  ASTLscal by using "with"
   */
  override def treeIfy(usedTwice: AstPred, repr: Map[AST[_], String]): ASTBt[R] = {
    val rewrite: rewriteASTBt[R] = (d: ASTBt[R]) => d.treeIfy(usedTwice, repr)
    val newD: ASTBt[R] = if (usedTwice(this)) new Read[R](repr(this))(mym) with ASTBt[R]
    else this match {
      case a: ASTB[R] => a.propagateASTB(rewrite)
      case _ => this.asInstanceOf[AST[_]] match {
        case Param(_) => new Read[R]("p" + repr(this))(mym) with ASTBt[R]
        case l: Layer[_] => new Read[R](AST.lify(repr(this)))(mym) with ASTBt[R]
        case Read(_) => this //throw new RuntimeException("Deja dedagifié!")
        case Delayed(arg) => //arg.asInstanceOf[ASTLt[L, R]].propagate(rewrite)
          arg().asInstanceOf[ASTBt[R]].treeIfy(usedTwice, repr) //the useless delayed node is supressed
        case Call1(f, a) => new Call1(f.asInstanceOf[Fundef1[Any, R]], a.asInstanceOf[ASTBg].treeIfy(usedTwice, repr))(mym) with ASTBt[R]
        case Call2(f, a, a2) => new Call2(f.asInstanceOf[Fundef2[Any, Any, R]],
          a.asInstanceOf[ASTBg].treeIfy(usedTwice, repr),
          a2.asInstanceOf[ASTBg].treeIfy(usedTwice, repr))(mym) with ASTBt[R]
      }
    }
    newD.setName(if (repr.contains(this)) repr(this) else this.name);
    newD.asInstanceOf[ASTBt[R]]
  }

  /** */
  def simplify(usedOnce: Set[String], defs: Map[String, Instr]): ASTBt[R] = {
    val rewrite: rewriteASTBt[R] = (d: ASTBt[R]) => d.simplify(usedOnce, defs)
    this match {
      case a: ASTB[R] => a.propagateASTB(rewrite)
      case _ => this.asInstanceOf[AST[_]] match {
        case r@Read(x) =>
          if (usedOnce.contains(x)) {
            val newr = defs(x).exps(0).asInstanceOf[ASTBt[R]]
            newr.name = r.name
            newr
          }
          else this
        case Call1(f, a) => new Call1(f.asInstanceOf[Fundef1[Any, R]], a.asInstanceOf[ASTBg].simplify(usedOnce, defs))(mym) with ASTBt[R]
        case Call2(f, a, a2) => new Call2(f.asInstanceOf[Fundef2[Any, Any, R]],
          a.asInstanceOf[ASTBg].simplify(usedOnce, defs),
          a2.asInstanceOf[ASTBg].simplify(usedOnce, defs))(mym) with ASTBt[R]
      }
    }
  }

  def isTm1: Boolean = false

  def isMap1Read: Boolean = false

  override def isNotTm1Read: Boolean = true

  /** returns the set of tree whose father  iterates the list of bits forming the integer,
   * in the inverse direction i.e. dirNarrowed goes
   * from leftward to rightward or from rightward to leftward
   * also narrows the direction if needed otherwise leave direction as Both */

  def SetDirAndReturnChangedDir(): Set[ASTBg] = {
    var r: HashSet[ASTBg] = HashSet.empty
    if (!isInstanceOf[ParOp[_]]) return r
    val me = asInstanceOf[ParOp[_]]
    val myDir = me.dirNarrowed
    var dirs: HashSet[Dir] = HashSet(myDir)
    for (s <- inputNeighbors) {
      r = r.union(s.asInstanceOf[ASTBg].SetDirAndReturnChangedDir()) //retrieves already found inverted directions
      if (s.isInstanceOf[ParOp[_]])
        dirs = dirs + s.asInstanceOf[ParOp[_]].dirNarrowed
    }
    if (dirs.contains(ASTB.Left()) && dirs.contains(ASTB.Right())) {
      r = r ++ inputNeighbors.filter(_.asInstanceOf[ParOp[_]].dirNarrowed == myDir.narrowed.opposite).asInstanceOf[List[ASTBg]]
      me.dirNarrowed = myDir.narrowed
    }
    else if (dirs.contains(ASTB.Left()))
      me.dirNarrowed = ASTB.Left()
    else if (dirs.contains(ASTB.Right()))
      me.dirNarrowed = ASTB.Right()
    r
  }


  def nBit(gen: CodeGen, env: HashMap[String, ASTBt[B]]): Int = {
    var paramBitSize = immutable.HashMap[AST[_], Int]()
    paramBitSize = paramBitSize ++ env.map((f: (String, ASTBt[B])) => (Param(f._1)(repr(f._2.ring)) -> (f._2.nBit(gen, env))))
    nBitR(paramBitSize, this, mutable.HashMap.empty[Param[_], Int], gen)
  }
}


