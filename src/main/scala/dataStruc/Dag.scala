package dataStruc

import compiler.ASTB.Both
import compiler.ASTBfun.ASTBg
import compiler.Circuit.iTabSymb
import compiler.{AST, ASTB, Affect, Instr}

import java.lang
import java.lang.System
import scala.Console.out
import scala.collection.{Map, mutable, _}
import scala.collection.immutable.{HashMap, HashSet, ListSet}
import scala.jdk.CollectionConverters._


object Dag {
  def apply[T <: DagNode[T]]() = new Dag(List[T]())
  def apply[T <: DagNode[T]](g: List[T]) = new Dag(g)



}

/**
 * Represents an entire Directed acylic Graph
 *
 * @param generators optional initial generators
 * @tparam T
 */
class Dag[T <: DagNode[T]](generators: List[T]) {
  //TODO put all the fields in the constructor to avoid recomputing when transtlatin dag[Instr] into DagInstr

  /**
   * creates empty Dag
   */
  def this() = this(List())

  /** We create an exeption which can store the cycle
   * in order to be able to print it nicely later
   * nicely means with names  identifying fields in the client program */
  class CycleException(val cycle: Vector[T]) extends Exception("cycle is detected, depth increase from left to right\n " +
    "a Tranfer fields y such as defVe is used in two separate expression, e1, and e2, which then get merged in a single Transfer zone $z$.\n " +
    "furthermore e2 uses an output x produced by e1\n " +
    "as a result, the zone of x has a link from z and a link to z\n " +
    "solution is to define a macro for processing of y, and call the macro" +
    "this will split back zone z. " +
    "fuuuuuck\n " + cycle) {}


  /**   all the generators -maximal elements- from which all the other can be reached
   * TODO checks that elements in allGenerators are indeed maximal elements.
   * */
  var allGenerators: List[T] = List() //TODO maintain nonGenerator together with allGenerator, and forget visitedL

  /** @return non maximal dag's element, assuming maximals have been stored in allGenerators. */
  def nonGenerators(): List[T] = {
    val aG = HashSet.empty[T] ++ allGenerators
    visitedL.filter(!aG.contains(_))
  }

  /** all visited dag's node, are in topological order due to initial depth first search, (starting  with generators first) */
  var visitedL: List[T] = List()

  /** newly visited node */
  private var newVisitedL: List[T] = List()
  /** the set version of visitedL */
  private var visitedS: Set[T] = ListSet()
  addGreaterOf(generators) //visits all the Dag's nodes
  def toStringOld = allGenerators.map(_.toStringTree).mkString("\n")

  override def toString: String = // "there is " + visitedL.length + " DagNodes\n" +
    visitedL.reverse.map((i: DagNode[T]) => i.toString()).mkString("")

  /**
   * add new generators to the Dag together with nodes which can be accessed from those.
   *
   * @param newGenerators generators possibly not in the DAG yet.
   * @return list of new node accessible from those newGenerators.
   *         TODO verifiez que c'est bien des générateurs
   */
  def addGreaterOf(newGenerators: List[T]): List[T] = {
    allGenerators ++= newGenerators
    //so that we can get which are the new nodes.
    newVisitedL = List()
    for (b <- newGenerators)
      dfs(b, Vector.empty) match {
        case Some(path) =>
          throw new CycleException(path)
        case None =>
      }
    visitedL = newVisitedL ::: visitedL
    newVisitedL //returns newly visited nodes.
  }

  /**
   * adds to  visitedS  and visitedL, nodes reachable from n, using a depth first search (dfs)
   * if a cycle is generated, returns the corresponding path.
   * When we use case hierarchy, keys associated to distinct node, can be identical, and this subtelty
   * means that not all the nodes are visited, there is a single representant for each equivalence class.
   *
   * @param n        node to test
   * @param visiting nodes being checked for adding to visited.
   * @return option type with a cycle is there is one. starting and ending with the same element found at a deeper place
   */
  def dfs(n: T, visiting: Vector[T]): Option[Vector[T]] = {
    if(n==null)
      throw new Exception(" probalement je fait référence a un champ pas encore calculé qui vaut donc null")
    if (visitedS(n)) return None
    else if (visiting.contains(n))
      return Some((visiting).drop(visiting.indexOf(n)) :+ n) //cycle returned
    else {
      val visiting2 = visiting :+ n
      for (e <- n.inputNeighbors)
        dfs(e, visiting2) match {
          case Some(c) => return Some(c)
          case _ =>
        }
      visitedS = visitedS + n;
      newVisitedL = n :: newVisitedL
    }
    None
  }

  /** @param called input from outside usage which must also be counted
   * @return set of Dag's elements which are at least two times input to another dag's element
   *         we produce a set in order to be sure to eliminate doublon, we thus loose the order */
  def inputTwice(called: Seq[T] = Seq.empty[T]): Set[T] = {
    val all = (visitedL.flatMap(_.inputNeighbors) ++ called) //multiset with repetition
    val all2: Predef.Map[T, List[T]] = all.groupBy(identity)
    /**
     *
     * @param fields identical fields differing only because some had the luch to get a name, and some not.
     *               this is because we use case class with name, and two instance are equals if they differ only from  the name.
     * @return the field which has the best name (shortest)
     */
    def bestNamed(fields: List[Named]):Named={
      var res=fields.head
      for(f<-fields.tail)
        if(res.name==null||(f.name!=null)&& (Naame.nbCap(f.name)<Naame.nbCap(res.name)))
          res=f
      res
    }
    /** we select the list of representant with a name, if possible */
  val res2=all2.flatMap  { case (k, v) ⇒ if(v.size>1)Some(bestNamed(v.asInstanceOf[List[Named]]).asInstanceOf[T]) else None}

   /* val nUser2 = immutable.HashMap.empty[T, Int] ++ all2.map { case (k, v) ⇒ k -> v.size } //computes multiplicity
    /** select groups whose size is >1 */
    val listInputTwice = visitedL.filter(e => nUser2.contains(e) && nUser2(e) > 1)
    val res = toSet(listInputTwice) //retains elements whose multiplicity is >=2*/
    res2.toSet
  }//.asJava

  /**
   * Adds attributes allowing to compute the union find algorithm
   *
   * @param elt
   */
  case class Wrap(elt: T) extends Union[Wrap]

  /**
   * applies the unionFind algorithme to compute connected components .
   *
   * @param testCycle true if we want to avoid cycles
   * @param p   predicate which defines adjacence beetween DagNodes
   * @param myWrap    mapping associating an element to its wrapping. it can be provided by the calling environment,
   *                  it it needs it
   * @result map associating a root to its component
   *         TODO redefinir a partir de indexed paquet
   */
  def indexedComponents(p: (T, T) => Boolean, testCycle: Boolean,
        myWrap: Map[T, Wrap] = immutable.HashMap.empty[T, Wrap] ++ visitedL.map(x => x -> Wrap(x))): (Predef.Map[T, List[T]], Set[(T, T)]) = {
    /** stores input neighbors which are roots, and stores it for roots,
     * so a T which is no longer root is not a key for inputneighbor root. */
    var intputNeighborRoots: Map[T, Set[T]] = null;
    if (testCycle) //we initialise the input roots to all input neighbors, because at the beginning, all the elements are roots.
      intputNeighborRoots = immutable.HashMap.empty ++ visitedL.map(x => x -> x.inputNeighbors.toSet)

    /** Computes the transitive closure of input neighbor roots.
     * it has not a good complexity if inputneibors are shared  */
    def inputNeihborRootsClosure(t: T): Set[T] = {
      /** calcule les voisins directs */
      val firstStage=
          if(intputNeighborRoots.contains(t))
                          intputNeighborRoots(t) //si t est  une root, on suppose que on a déja calculé les input root.
          else      //sinon faut chercher la racine, myWrap(t).root.elt
                  { val w=myWrap(t)
                    val r: Wrap =w.root
                    val e: T =r.elt
                    intputNeighborRoots(e)
                  }
      var result: Set[T] = firstStage  //intputNeighborRoots(t)
      for (input <-  firstStage  )       //intputNeighborRoots(t)
        result = result.union(inputNeihborRootsClosure(input))
      result
    }
    /** @return  computes  a union of  closures */
    def inputNeihborRootsClosuresSet(ts: Set[T]): Set[T] = if (ts.isEmpty) HashSet.empty else
      ts.map(inputNeihborRootsClosure(_)).reduce((x, y) => x.union(y))

    /** a cycle is created if src contains trueInputNeighborsClosure from input neighbors other than target, which contains target */
    var pairCausingCycles:Set[(T,T)]=new HashSet[(T, T)]()
    def cycleCreation(src: T, target: T) = { //todo a faire que si on cause un cycle.
      /** true if one far away input contains the output */
      val inrcimt=inputNeihborRootsClosuresSet(src.inputNeighbors.toSet - target)
      val inrcit=inputNeihborRootsClosuresSet(HashSet( target))
      //val r = inrcimt.contains(target) //first trial not sufficient, faut aussi faire jouer la fermeture transitive des inputs.
      val inrcit2=inrcit.union(HashSet(target)) //faut considérer l'element lui même, quand meme.
      val cycleDetected=inrcimt.intersect(inrcit2).nonEmpty
      if (cycleDetected) //look if there exists another path from target ot src, in which case unioning the two would create a cycle
       {
         println("making the union of " + src + "   to  " + target + "   was about to creating a cycle")
         pairCausingCycles =  pairCausingCycles + ((src,target))
       }
      cycleDetected
    }

    for (src: T <- visitedL)
      for (target: T <- src.inputNeighbors)
        if (p(src, target) && (!testCycle || !cycleCreation(src, target))) { //either we accept cycle, or we do not but there is none

          val rootoRemove = myWrap(src).union(myWrap(target)) //in case of a true union, we need to know which root is removed
          val newCommonRoot: T = myWrap(src).root.elt //computes a common root for elements of one component
          if (testCycle)
            rootoRemove match {
              case None => //the two merged nodes already add the same root, so nothing needs to be done.
              case Some(r) => //root r, is removed
                intputNeighborRoots = intputNeighborRoots + (newCommonRoot -> //la nouvelle racine issue de la fusion
                  (intputNeighborRoots(newCommonRoot) - r.elt).union(intputNeighborRoots(r.elt))) //a pour racine input, la réunion des ancien input, moin r.elt qui n'est plus une racine.
                intputNeighborRoots = intputNeighborRoots - r.elt
                val u = 0
            }
        }
    (visitedL.groupBy(myWrap(_).root.elt),pairCausingCycles)
  }


  /**
   * we apply the unionFind algorithm to compute connected components .
   *
   * @param p   predicate which defines adjacence beetween DagNodes
   * @param all mapping associating an element to its wrapping. itcan be provided by the calling environment, it it needs it
   * @result List of dagNodes of each component, as an iterable of iterable
   */
  def components2(p: (T, T) => Boolean, all: Map[T, Wrap] = immutable.HashMap.empty[T, Wrap] ++ visitedL.map(x => x -> Wrap(x))): (Iterable[List[T]], Set[(T, T)]) =
  { //on test si test cycle magically solve the cycle problem
    val (componentMap, cyclePair)=indexedComponents(p, true, all)
    (componentMap.values, cyclePair)
  }

}


