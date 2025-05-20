package compiler

import AST._
import ASTB.{Tminus1, shiftL, shiftR}
import ASTBfun.ASTBg
import Circuit._
import compiler.ASTLt.ConstLayer
import compiler.DataProg.{isRootMainVar, nameDirCompilLoops}
import compiler.SpatialType.BoolV
import dataStruc.{Named, Util}
import dataStruc.Util.{hierarchyDisplayedField, parenthesizedExp, prefixDash}
import sdn.{ MovableAg, MovableAgentV}
import sdn.Root4naming
import simulator.CAloops2

import java.io.File
import scala.collection.{mutable, _}
import scala.collection.immutable.HashMap
import scala.jdk.CollectionConverters._

/**
 *
 * @param p supplementary input parameters
 * @tparam L
 * @tparam R
 *
 * a circuit is implemented like a function definition, whose body is temporary undefined, and will be set to computeRoot
 * Analysed by the compiler to produce a CA rule,
 * parameter corresponds to externally generated fields input to  the CA
 * they must be present in the memory, before the main loop is called.
 * return results are fields produced by the CA, to be used by an host.
 * they are in the memory after the main loop is called.
 * Normally, it is the caller which decides where the result of the main are stored,
 * however, for the main, we can suppose the offset of Data Param starts at Zero.
 * the main's signature and those compiled offset must be accessible from the host.
 * We imagine that another compiler towards 1D can be used to do the interface: produce the 2D input and read the 2D output, on the border
 * both 1D and 2D compilation can be linked, as far as offset computation goes.
 * In turns, the 1D CA takes input output fields produced by the host, on a single cell (or on four corners)
 */
abstract class Circuit[L <: Locus, R <: Ring](p: Param[_]*) extends AST.Fundef[(L, R)]("main", null, p: _*) {
  /**
   * contains name of macro which needs being recompiled, because allthough they were already compiled, they are now needed for a distinct number of bits
   * Emblematic example is the distance which is used for 3 bits, but also 5bits integers.
   */

  /** to be defined in the circuit for collecting all the nodes participating in usefull computation,   "abstract def" because known latter */
  def computeRoot: ASTLt[L, R]
  val root4naming:Named=null //on donne une valeur pour pouvoir toujours compiler les ca monocouche
  val nameCAlowerCase:String=null //on donne une valeur pour pouvoir toujours compiler les ca monocouche

  /**
   * Compiles the circuit
   * Algorithm of compilation generates big maps used temporarily such as usedmorethanonce, to update a state.
   * after generating the instruction,  the state is contained in  three  maps: allinstructions,  affectmap, fundef
   * after computing nbit, we then have 1-a table which tells how much bits are used for each symbol
   * 2-a table  which tells for each expression, how much bits is needed to store them.
   *
   */

  def compile(m: Machine):CAloops2 = {
    body = computeRoot //we pretend that the circuit is a function which returns compute Root
    val prog1: DataProg[InfoType[_]] = DataProg(this,root4naming,nameCAlowerCase);
   // print(prog1)

    val prog2 = prog1.treeIfy();
    //    print("222222222222222222222222222222222222222222222222222222222222222222222222222222222\n" + prog2);

    val prog3: DataProg[InfoType[_]] = prog2.procedurIfy();
    //   print("3333333333333333333333333333333333333333333333333333333333333333333333\n" + prog3);

    val prog4: DataProg[InfoNbit[_]] = prog3.bitIfy(List(1)); //List(1)=size of int sent to main (it is a bool).
    //   print("44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444\n" + prog4 + "\n\n")

    val prog5: DataProg[InfoNbit[_]] = prog4.macroify();
    //  println("macroIfy55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555\n" + prog5 + "\n\n")

    val prog5bis: DataProg[InfoNbit[_]] = prog5.addParamRtoDagis2();
     //print("addParamRtoDagis255555555555555555555555555555555555555555555555555\n" + prog5bis + "\n\n")

    val prog5ter: DataProg[InfoNbit[_]] = prog5bis.radiusify3
    //print("radiusify555555555555555555555555555555\n" + prog5ter)

    val prog6 = prog5ter.unfoldSpace(m); //ajouter les tm1s!!
      print("unfoldSpace666666666666666666666666666666666666666666666666666666666666666666666666666666666666\n" + prog6 + "\n\n")

    val prog7 = prog6.treeIfy(); //spatiall unfolding generates reused expression that need to be affected again
    //print("treeIfy777777777777777777777777777777777777777777777777777777777777777777777777777777777777777\n" + prog7 + "\n\n")

    val prog7bis = prog7.simplify(); //this will remove id which are read only once.
    // print("simplify777777777777777777777777777777777777777777777777777777777777777777777777777777777777777\n" + prog7bis + "\n\n")

    val prog8: DataProg[InfoNbit[_]] = prog7bis.detm1Ify() //Will also generate instruction store and remove tm1 when applied just before storing, transforming it into an integer argument.
    //  print("detm1ify 8888888888888888888888888888888888888888888888888888888888888888888888888\n" + prog8 + "\n\n")

    val prog10: DataProgLoop[InfoNbit[_]] = prog8.loopIfy()
    // print("loopify1010101010101010101010101010101010101010" + prog10)

    val prog11: DataProgLoop[InfoNbit[_]] = prog10.unfoldInt()
 // print("unfold int 111111111111111111111111111111111111111111111111111111111111\n" + prog11)
    val prog12: DataProgLoop[InfoNbit[_]] = prog11.coaalesc() //allocates memory
    //System.out.println(prog12.allLayers)
   print("\ncoalesccoalesccoalesccoalesccoalesccoalesccoalesc121212121212121212121212121212121212121212121212\n" + prog12)
   // ("\n\n\n javajavajavajavajavajavajavajava\n" + prog12.asInstanceOf[ProduceJava[InfoNbit[_]]].produceAllJavaCode)
    //as a result of compiling, compiledCA is available and will be read by the simulator, so we just launch it.
   // val s=new simulator.Simulator()   s.AppletLauncher()
    prog12.asInstanceOf[ProduceJava[InfoNbit[_]]].produceStoreAndCompileAllJavaFile
  }
}


object Circuit {
  final case class NbOfBitIntoAccountException(private val message: String = "",
       private val cause: Throwable = None.orNull)
    extends Exception(message, cause)
  /**updated during first pass with names of fun such as gradslope, which which  need to be compiled during a second pass because of a  new bitsize*/
  var takeNbOfBitIntoAccount:Set[String]=immutable.HashSet()
  /** we restrict ourself to circuit returning a boolV, for the moment */
  def main(args: Array[String])= {
    compiledCA(args(0))
    ()
  }

  /**
   *
   * @param nameCA name of the CA program
   *               returns an instance of CAloops2 that does he convolution, ready for simulation
   *               It is called either for a static compilation, or dynamically from the simulator
   */
  def compiledCA(nameCA:String):CAloops2={
   val myCircuit = new Circuit[V, B]() {
     /** from the AST given, we are able to reconstruct all the layer, plus system instructions.  */
     /** class name specified for compilation*/
     val rootClass=Class.forName("progOfCA." + nameCA)
     /**  creates an instance object*/
     /** The root4naming is wrapping the agent, so as to enable its declaration sooner and break a dependency cycle */
     val wrappe4naming=new Root4naming()
     override val root4naming: Named =  wrappe4naming//rootObject
      val rootObject: Named= rootClass.getDeclaredConstructor().newInstance().asInstanceOf[Named]
     wrappe4naming.setRootMustruct(rootObject) //now we can

     /** rootObject which will be the root for naming. Everything that we want to display must be accessibe from the root objec*/
     override val nameCAlowerCase=nameCA.toLowerCase
     /** rootAST contains all the code, its location depends on the program category, wether we have a single layer, a single  agent,  or a system of agent */
     val rootAst:ASTLt[V, B]=rootObject match {  //
          case ast:BoolV
             =>   ast  //if we have a single layer CA, by convention it is a boolV, and also  the root Ast
          case ag:MovableAg[V] with MovableAgentV
             =>ag.is //if we have a single agent,  the update of its chi layer is the rootAST, therefore, it has to need  all the other layers.
      }
      def computeRoot = rootAst
    }
    var notCompiled=true; var limit=0 //evite la boucle trop grosse
    var result:CAloops2=null
   while(notCompiled&&limit<10)
       try { notCompiled=false;result=myCircuit.compile(hexagon)} //autre tour de manége, avec plus de fun a compiler
    catch{
      case e: NbOfBitIntoAccountException=>
        notCompiled=true;limit+=1
        assert(limit<10,"y a eu plus de 10 fonctions a recompiler avec une différente bit size, ca commence a faire beaucoup, faut regarde de plus prés ckiskispasse")
        isRootMainVar=true  //on refait un tour de manége, this boolean is initially true for the first fun which is the main, and then flipped to false
           //the second time it will more likely work because compilation of slopeDelta will be enforced due to seeting of takeNbOfBitIntoAccount
    }
  result
  }


  
  type TabSymb[T] = mutable.HashMap[String, T]
  type AstMap[T] = mutable.HashMap[AST[_], T]
  type TabConstr = TabSymb[Constraint]
  type iTabSymb[T] = Map[String, T]
  type iTabSymb2[T] = immutable.HashMap[String, T];
  type iAstField[T] = Map[AST[_], T]
  /** spatial unfolding of an ASTL of "simplicial" type creates an array of array of ASTB.
   * The cardinal of first array is 1,2,3 for V,F,E,  */
  type ArrAst = Array[ASTBg]
  /** spatial unfolding of an ASTL of "transfer type" creates an array of array of ASTB. The cardinal of first array is 1,2,3 for V,F,E, the seconds array is 6,3,2  */
  type ArrArrAstBg = Array[Array[ASTBg]]
  /**
   * The only place where a machine differs from another is when compiling the transfer function,
   * it is parameterised by One function for each pair of simplicial type.
   * Type of input is transfer(src,des) type of output is transfer(des,src) , where "src" is first S, and "des" is second S
   */
  type Machine = (S, S, ArrArrAstBg) => ArrArrAstBg
  /** correspondance between suffix and index */
  val order: HashMap[String, Int] = immutable.HashMap("w" -> 0, "nw" -> 1, "ne" -> 2, "e" -> 3, "se" -> 4, "sw" -> 5,
    "wn" -> 0, "n" -> 1, "en" -> 2, "es" -> 3, "s" -> 4, "ws" -> 5,
    "h" -> 0, "d" -> 1, "ad" -> 2,
    "h1" -> 0, "h2" -> 1, "d1" -> 2, "d2" -> 3, "ad1" -> 4, "ad2" -> 5,
    "do" -> 0, "up" -> 1,
    "dop" -> 0, "dob1" -> 1, "dob2" -> 2, "upp" -> 3, "upb1" -> 4, "upb2" -> 5,
    "dob" -> 0, "dos1" -> 1, "dos2" -> 2, "upb" -> 3, "ups1" -> 4, "ups2" -> 5)
  val transfers: List[(S, S)] = List((V(), E()), (E(), V()), (V(), F()), (F(), V()), (E(), F()), (F(), E()))


  /**
   * The hexagon machine models communication according to the perfect hexagonal grid.
   * diagonal (d1,d2) and antidiagonla (ad1,ad2) are oriented
   * so that all the shift and delay gets applied on d1 (up), so that the same computation is applied
   * on d2 and ad2, when the vE fields is obtain by a broadcast followed by a transfer.
   * voir commentaire du code sur l'emplacement des tm1s par rapports au shift, faudra générer cela de facon otoMatik!
   */

  import ASTB.tm1

  val hexagon: Machine = (src: S, des: S, t: ArrArrAstBg) => {
    implicit val scalarType: repr[_ <: Ring] = t(0)(0).mym;
    src match {
      case V() => des match {
        case E() => /*Ve->Ev*/
          // val Array(e, ne, nw, w, sw, se) = t(0)
          val Array(e, se, sw, w, nw, ne) = t(0) //on utilise un seul tableau 1D pour vertex
          Array(Array(tm1(e), tm1(shiftL(w))), Array(tm1(se), nw), Array(tm1(sw), shiftR(ne))) //ici on pousse les tm1s vers la fin pour factoriser les tm1 dans transfer(broadcast) de V vers vE
        case F() => /*Vf->Fv*/
          val Array(se, s, sw, nw, n, ne) = t(0);
          Array(Array(n, tm1(shiftL(sw)), tm1(se)), Array(tm1(s), shiftR(ne), nw))
        //Array(Array(n, tm1(sw), tm1(se)), Array(tm1(shiftL(s)), ne, shiftL(nw)))
      }
      case E() => //un seul tableau 2D pour Edge
         val Array(Array(h1, h2), Array(d1, d2), Array(ad1, ad2)) = t; //todo consider renaming d and ad by o  and ao, 'o' for oblique

        des match {
          case V() => /*vE->eV*/
            Array(Array(h1, d1, ad1, shiftR(h2), tm1(d2), tm1(shiftL(ad2)))) //ici au contraire on met tm1 au début pour factoriser les tm1 dans reduce(broadcast de vE vers V
          case F() => /*Ef->Fe*/
            Array(Array(tm1(h2), tm1(shiftL(ad2)), tm1(d1)), Array(shiftR(h1), tm1((ad1)), tm1(d2)))
        }
      case F() => des match {
        case V() => /*Fv->Vf*/
          val Array(Array(dp, db1, db2), Array(up, ub1, ub2)) = t;
          Array(Array(db2, up, shiftR(db1), tm1(ub2), tm1(dp), tm1(shiftL(ub1))))
        case E() => /*eF->fE*/
          val Array(Array(db, ds1, ds2), Array(ub, us1, us2)) = t;
          Array(Array(tm1(shiftL(ub)), db), Array(ds2, us2), Array(us1, shiftR(ds1)))
      }
    }
  }

  /** generates an input array */
  def inAr(s1: S, s2: S): ArrArrAstBg = {
    var i = -1;
    def nameInt = {
      i += 1;
      "" + i
    };
    def myp() = new Param[B](nameInt) with ASTBt[B];
    Array.fill(s1.density)(Array.fill(6 / s1.density)(myp()))
  }

  /** automatically computes permutation implied by hexagon */
  val hexPermut: immutable.Map[(S, S), Array[Int]] = immutable.HashMap.empty ++ transfers.map((ss: (S, S)) => ss -> {
    val (s1, s2) = ss;
    val t = Circuit.hexagon(s1, s2, inAr(s1, s2));
    val l = t.map(_.toList).toList.flatten; //compute the permutation of T[S1,S2] => T[S2,S1]
    val r = new Array[Int](6);
    var i = 0;
    for (a <- l) {
      r(i) = a.symbolsExcepLayers.head.toInt; i += 1
    };
    r
  })

  //print(hexPermut)
}

