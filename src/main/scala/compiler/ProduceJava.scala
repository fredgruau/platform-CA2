package compiler

import compiler.AST.Read
import compiler.ASTB.{False, True, nbitExpAndParam}
import compiler.Circuit.{TabSymb, compileJavaFiles, compiledCA, iTabSymb}
import compiler.DataProg.{nameDirCompilCA, nameDirCompilLoops, nameDirProgLoops}
import compiler.Instr.deployInt2
import compiler.Locus.{all2DLocus, allLocus}
import compiler.ProduceJava.totalGateCount
import compiler.TestCompile.path
import dataStruc.Util.{CustomClassLoader, append2File, copyArray, hasBeenReprogrammed, hierarchyDisplayedField, loadClassAndInstantiate, methodName, myGetDeclaredMethod, parenthesizedExp, radical, radicalOfVar, radicalOfVar2, radicalOfVarIntComp, radicalOfVarRefined, radicalRad, removeAfterChar, rootOfVar, sameRoot, shortenedSig, writeFile}
import compiler.VarKind.LayerField
import dataStruc.{Named, Util}
import dataStruc.Named.{isLayer, noDollarNorHashtag, noHashtag}
import javaxtools.compiler.{CharSequenceCompiler, UseCompiler}
import simulator.CAloops2
import simulator.SimulatorUtil
import simulator.XMLutilities.readXML

import java.io.File
import java.lang.reflect.Method
import java.util.regex.Pattern
import scala.::
import scala.collection.IterableOnce.iterableOnceExtensionMethods
import scala.collection.convert.ImplicitConversions.`collection asJava`
import scala.collection.{Map, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import scala.jdk.CollectionConverters._
import scala.util.Random
import scala.xml.{Elem, Node, NodeSeq, XML}
object ProduceJava{
  /** will contain the gate count, once the calls have been compiled */
  var totalGateCount=0
}
/** provide method in order to  produce the final java code */
trait ProduceJava[U <: InfoNbit[_]] {
  self: DataProgLoop[U] =>
  /** returns  a big string  storing the code for CAloops, and the code for main calling those CAloops on arrays */
  def produceAllJavaFile:CAloops2 = { //we need to generate spatial signature for macros before we can adress the main.
    val leafLoops = subDataProgs.filter(p => p._2.isLeafCaLoop) //si pas recompilé yaura pas tout!
    val codeLoops: iTabSymb[String] = leafLoops.map({ case (k, v) => (k -> v.asInstanceOf[ProduceJava[U]].javaCodeCAloop(k)) }) //retrieves all the recompiled CA loops
    val (codeLoopsMacro, codeLoopsAnonymous) = codeLoops.partition({ case (k, v) => !k.startsWith("_fun") }) //anonymous functions start with _fun



  /*  val PACKAGE_NAME = "compiledCA"

    val r = new Random()
    val randClassName = "" + Math.abs(r.nextInt % 1000)
    val qName = PACKAGE_NAME + '.' + nameCA.capitalize //+ randClassName
 */
    //we now process non anonymous macro loop
     val grouped: Predef.Map[String, Map[String, String]] = codeLoopsMacro.groupBy({ case (k, v) => k.substring(0, k.indexOf(".")) }) //  what comes before the dot is the name of the class where to regroup macros



    /** contains the loops but also many other parameters */
    var codeAllLoops = ""
    val classPath = "target/scala-2.13/classes/"
    // Create a new instance of the custom class loader
    val customLoader = new CustomClassLoader(classPath)

    for (macroLoopName <- grouped.keys) { //for loops, the code is distributed in several file, for clarity. We handle each one, one by one
      val macroLoopPath = nameDirCompilLoops +macroLoopName+ ".java"
      //we compare date of creation of progOfMacro/filename with compiledMacro.filename, if it is more recent we have to reproduce it all, so we just erase it.
      //if(hasBeenReprogrammed(k4,nameDirProgLoops,nameDirCompilLoops))
        if (hasBeenReprogrammed(nameDirProgLoops+macroLoopName.capitalize+".scala",macroLoopPath)) //there has been a reprogramming
        {val f=new File( macroLoopPath)
         f.delete()
        }
      //if macro file does not exists, creates it (preambule + macroLoopName + "{\n" + notYetDefined.values.mkString("\n") + postambule).replace('#', '$'); //'#' is not a valid char for id
      val alredyDef: Set[String] =   //contient "rand_1"
        if (!new File( macroLoopPath).exists())
        { //this is a brand new set of macros
          val preambule = "package compiledMacro;\n import simulator.PrShift;\n public class "
           writeFile( macroLoopPath, preambule + macroLoopName + "{\n }") //new compiled java macro will be inserted just before last acolades.
           new HashSet[String]() //there is no macro yet defined, since the class was not even existing (brand new)
       }
        else
          myGetDeclaredMethod("compiledMacro." + macroLoopName).toSet //class names contains a dot instead of an antislash
      val notYetDefined: Map[String, String] = grouped(macroLoopName).filter(x => !alredyDef.contains(x._1.drop(x._1.indexOf(".") + 1))) //name of the macro = we drop what's before the dot
      //we generate the code of the loops correcponding to k4 keys

      if (notYetDefined.nonEmpty) {
        val codeK4Loops = (notYetDefined.values.mkString("\n")).replace('#', '$'); //'#' is not a valid char for id
        codeAllLoops = codeK4Loops + codeAllLoops  //codeAllLoops is just for printing
        append2File(macroLoopPath, codeK4Loops) //we add the code of the macro which was not yet defined.
        //we compile the macro before the main.
        val compilationSuccess = compileJavaFiles(List(macroLoopPath))
        assert(compilationSuccess," compilation macro: "+macroLoopPath+" planté, poil au nez")
        System.out.println(" compilation macro: "+macroLoopPath+" reussie")
        val loadedClassC = customLoader.findClass("compiledMacro." + macroLoopName) //we reload the class so that the compmiler of main can access the new macros
      }
    }
    val codeMain: String = javaCodeMain(codeLoopsAnonymous.values.mkString("\n")).replace('#', '$'); //'#' is not a valid char for id
    val nameCA = radicalOfVar(paramR(0)) + "CA" //name of the produced java file is equal to the name of the layer wrapping around all the compiled prog
    val nameCAjava = nameCA.capitalize + ".java"
    writeFile(nameDirCompilCA+nameCAjava, codeMain + "\n") //stores the code of the main (with anonmymous loop)
    val sourceFiles = List(nameDirCompilCA+nameCAjava)
    val compilationSuccess = compileJavaFiles(sourceFiles)
    assert(compilationSuccess,"compilation of main CA:"+nameDirCompilCA+nameCAjava+ " a planté, poil au nez")
    System.out.println("compilation of main CA:"+nameDirCompilCA+nameCAjava+ " a réussi")
    val classCA: Class[_] =customLoader.findClass("compiledCA." + nameCA.capitalize) //we reload the just compiled class
    val progCA=loadClassAndInstantiate("compiledCA." + nameCA.capitalize,customLoader)
    progCA.asInstanceOf[CAloops2]
   //val compiledCA= UseCompiler.newCA(codeMain, qName) //compile the CA, after generating the macro loop, retrieve the bytecode
 /*       //when there are new loops, it will fail, but at least we have store those new loops before.
    assert(compiledCA!=null," ouaips, ca a planté, poil au nez") //si ca plante pas besoin de retourner au simulateur
     compiledCA //we return the compiled CA to the simulator.
    //"" + codeMain + codeAllLoops //returns for direct printing*/
  }

  /**
   *
   * @param nameMacro name of a macro CAloop, should be removed the reds. if dot is present
   * @return codes of the loop
   */
  def javaCodeCAloop(nameMacro: String): String = {
    val shortSigIn = shortenedSig(paramD);
    val shortSigOut = shortenedSig(paramR)
    val localSpatialLayers = tSymbVar.filter(x => x._2.k.isLayerField && noDollarNorHashtag(x._1))
    val layerNames = localSpatialLayers.keys.toSeq.sorted.toList


    val templateURL=if(nameMacro.startsWith("_fun"))
      "src/main/java/compiledCA/template/templateCAloop2.txt"
    else
      "src/main/java/compiledCA/template/templateCAloop.txt"  //for macroLoop, we need to store the gatecount


    val gateCount=
     // if(nameMacro.startsWith("_fun"))
             gateCountMacroLoop
    //  else   dataStruc.Util.readStaticField("compiledMacro."+radical( nameMacro ) , methodName(nameMacro)+"GateCount")//we need to read a static  "slopDelta_3_1_2_1_1GateCount"  in class "compiledMacro.grad"

    //we proceed by filling slot in a template named templateCAloop.txt, each slot is filled using a specific method
    replaceAll(templateURL, Map(
      "GATECOUNT" -> {gateCount.toString },
      "NAMEMACRO" -> {
        def removeBeforeDot(s: String): String =
          if (s.contains('.')) //this is indeed not an anomymous macro
            s.drop(s.indexOf(".") + 1)
          else s

        removeBeforeDot(nameMacro)
      },
      "PARAMETERS" -> {
        /** add type to parameters, either int[] or int[][],
         * one dimension is enough for spatial type boolV, two dimensions are needed for other locus */
        def javaIntArray(s: String) = (if (isBoolV(s)) ("int [] ") else ("int [][] ")) + s

        val parameters = (shortSigIn ::: (shortSigOut ::: layerNames)).map(javaIntArray(_))
        parameters.mkString(",")
      },
      "ANCHORPARAM" -> {
        /** @param shortened name of spatial parameters
         * @param original   names of scalar parameters, in same order
         * @return Produce the code to inintialize 1D array from 2D arrays */
        def anchorParam(shortened: List[String], original: List[String]): List[String] = {
          var res: List[String] = List();
          var i = 0
          for (s: String <- shortened) {
            if (isBoolV(s))
              i += 1 //no need to anchor, parameter is already a 1D arrau
            else {
              var j = 0; //j iterates on the indexes of the different scalar componendt
              try while (radicalOfVar(original(i)) == s) { //we scan through the parameter having same radical
                res = original(i) + "=" + s + "[" + j + "]" :: res;
                j += 1;
                i += 1 //affect each scala component
              } catch {
                case _: IndexOutOfBoundsException =>
              }
            }
          }
          res
        }

        //we anchor data parameters, result parameters, and constant def layers.
        val anchor = (anchorParam(shortSigIn, paramD) ::: anchorParam(shortSigOut, paramR) ::: anchorParam(layerNames, layerNames.flatMap(s => tSymbVar(s).locus.deploy(s)))).reverse.mkString(",")
        if (anchor.size > 0) "int[] " + anchor + ";" else "" //we may not need to anchor anything.
      },
      "PROPAGATEFIRSTBIT" -> {
        val callsToPropagate: Seq[String] = paramD.map((s: String) => "p.prepareBit(" + s + ")") //for the moment we do the propagation on all data parameters
        val callsToPropagate2 = shortSigIn.map((s: String) => "p.prepareBit(" + s + ")")

        val callsToMirror = shortSigIn.map((s: String) => {
          val l = tSymbVar(s).t.asInstanceOf[(Locus, Ring)]._1
          "p.mirror(" + s + ",compiler.Locus." + l.javaName + ")"
        })
        callsToMirror.mkString(";") + ";\n" + callsToPropagate2.mkString(";") + "\n"
      },

      "CALINENUMBER" -> (paramD ::: paramR)(0), //There must be at least one param,we need to read it so as to know the length which is the number of CA lines.
      "DECLINITPARAM" -> {
        /** declares all the variables local to the loops, and initializes them to zero if needed */
        def declInitParam = {
          /** variable which are delayed must be indentified so as to be initialized */
          def isDelayed(s: String): Boolean = {
            val res = delayed.contains(removeAfterChar(s, '#'))
            //System.out.println(delayed)
            res
          }

          val testCoalesc = coalesced
          val intReg = (standaloneRegister ++ coalesced.keys).filter(noHashtag(_)) //should be declared todo gestion plus precise des dieses
          // val intReg = (standaloneRegister ++ coalesced.keys).filter(noDollarNorHashtag(_)) //should be declared todo gestion plus precise des dieses
          val boolReg: Iterable[String] = intReg.flatMap((s: String) => deployInt2(s, tSymbVarSafe(s))) //intReg which have a single component are not deployed

          boolReg.toList.sorted.map((s: String) => if (isDelayed(s) || true) s + "=0" else s).mkString(",") //todo preciser keski est delayed
        }

        val dip = declInitParam;
        if (dip.size > 0) "// initialisation \n int " + dip + ";" else ""
      },
      "LOOPBODY" -> {
        /* val t = totalCode
         val removeFalse = t.filter(e=> e != False()&&e != True()) */
        //certaine expression se simplifie sur false ou true

        // totalCode.map(_.toStringTreeInfix(tSymbVar.asInstanceOf[TabSymb[InfoType[_]]])).grouped(4).map(_.mkString(";")).mkString(";\n ")
        totalCode.map(_.toStringTreeInfix(this.asInstanceOf[DataProg[InfoType[_]]])).grouped(4).map(_.mkString(";")).mkString(";\n ")
      }
    ))
  }

  /**
   *
   * @param codeLoopAnonymous this code is grouped together with the main, in order to be only accessible from this mainCA list of calls
   * @return write in the mainCA file the code of the main plus the anonymous, and in the loopFile, the code of the macro
   *
   */
  def javaCodeMain(codeLoopAnonymous: String): String = {
    /**
     *
     * @param tSymbVarAndConstLayer tSymbVar plus names of constant Layers defined in subProgram (should be declared in the main)
     * @return list of offset for all named fields. Used for 1-to anchor named 1D arrays, 2-to list memory planes
     * */
    def offsetsInt(tSymbVarAndConstLayer: iTabSymb[InfoNbit[_]]): Map[String, List[Int]] = {
      tSymbVarAndConstLayer.map { case (k, v) => (k,
        //   if (v.t == (V(), B()) /*|| v.t == B()*/)   List(adress(coalesc(k))) else
        {
          val offsetstring = v.locus.deploy2(k, tSymbVarSafe(k))
          for (of <- offsetstring)
            if (!coalesc.contains(of))
              throw new Exception("trouve pas " + of + " dans coalesc")
          offsetstring.map((s: String) => adress(coalesc(s))).toList
        })
      }
    }

    val spatialOfffsetsInt = offsetsInt((tSymbVar ++ layerSubProgStrict).filter(x => noDollarNorHashtag(x._1)))
    // val spatialOfffsetsIntMain = offsetsInt((tSymbVar ++ layersMain).filter(x => noDollarNorHashtag(x._1)))
    val (theCallCode: Seq[String], decompositionLocus, theDisplayed) = javaOfTheCallInTheMain()

    def initLayer(spatialLayer: Map[String, InfoNbit[_]]): HashMap[String, String] = {
      HashMap[String, String]() ++ spatialLayer.map({ case (s, i) => (s -> i.k.asInstanceOf[LayerField].init) })
    }

    def anchorOneVar(oneVar: (String, List[Int])) = {
      val ints = oneVar._2
      var res = ints.map("m[" + _ + "]").mkString(",")
      if (!isBoolV(oneVar._1))
        res = " new int[][]{" + res + "}" //we have a 2D array
      res = oneVar._1 + "=" + res;
      res
    }

    // def javaIntArray(s: String) = (if (isBoolV(s)) ("int [] ") else ("int [][] ")) + s


    def anchorNamed(offset: Map[String, List[Int]]): String = {
      val (offset1D, offset2D) = offset.partition(x => isBoolV(x._1)) //x._2.size == 1)
      (if (offset1D.nonEmpty) "int[]" + offset1D.map(anchorOneVar(_)).mkString(",") + ";\n" else "") +
        (if (offset2D.nonEmpty) "int[][]" + offset2D.map(anchorOneVar(_)).mkString(",") + ";\n" else "")
    }

    //we use the same template technique as the one used for CAloops
    replaceAll("src/main/java/compiledCA/template/templateCA.txt", Map(
      "GATECOUNT" -> totalGateCount.toString,//totalOp.toString,
      "NAMECA" -> radicalOfVar(paramR(0)).capitalize,
      "MEMWIDTH" -> ("" + mainHeapSize), //TODO on calcule pas bien la memwidth)
      "DECLNAMED" -> {
        /** code that declares all the named arrays 1D and 2D */
        def DeclNamed(offset: Map[String, List[Int]]): String = {
          val (var1D, var2D) = offset.keys.partition(offset(_).size == 1) //we distinguish 1D arrays from 2D arrays.
          (if (var1D.nonEmpty) "int[]" + var1D.mkString(",") + ";\n" else "") +
            (if (var2D.nonEmpty) "int[][]" + var2D.mkString(",") + ";\n" else "")
        }
        ("" + DeclNamed(spatialOfffsetsInt))
      },
      "DECLNOTNAMED" -> {
        /** Codes that declares unamed arrays */
        def declNotNamed(decomposition: Map[Locus, Map[List[Int], Int]]): String = { //todo queskispass si c'est un tableau 1D?
          val var1D = (0 until decomposition(V()).size).map("V" + _) //name of unamed points to its locus.
          var var2D: List[String] = List() //needs 2D arrays
          for (l: Locus <- all2DLocus) {
            var2D = var2D ++ (0 until decomposition(l).size).map(l.shortName + _)
          }
          (if (var1D.nonEmpty) "int[] " + var1D.mkString(",") + ";\n" else "") +
            (if (var2D.nonEmpty) "int[][] " + var2D.mkString(",") + ";\n" else "")
        }

        ("" + declNotNamed(decompositionLocus))
      },
      "LISTCALL" -> {(theCallCode.reverse.mkString("\n"))+"\n\n\n"},
      "ANCHORNAMED" -> {
        /** code that anchors named arrays on memory */
        anchorNamed(spatialOfffsetsInt)
      },
      "ANCHORNOTNAMED" -> {
        /** Codes that decompose array 2D into memory slices */
        def anchorNotNamed(decomposition: Map[Locus, Map[List[Int], Int]]): String = { //todo queskispass si c'est un tableau 1D?
          var codeDecl: List[String] = List()
          for (l: Locus <- allLocus) if (decomposition(l).nonEmpty) {
            val (offset1D, offset2D) = decomposition(l).partition(x => x._1.size == 1) //separates  BoolV which are stored on one plane
            if (offset1D.nonEmpty) codeDecl ::= "int[]" + offset1D.map(x => anchorOneVar((l.shortName + x._2, x._1))).mkString(",") + ";\n"
            if (offset2D.nonEmpty) codeDecl ::= "int[][]" + offset2D.map(x => anchorOneVar((l.shortName + x._2, x._1))).mkString(",") + ";\n"
          }
          // seedE = new int[][]{m[8], m[9], m[10]};
          codeDecl.mkString("\n")
        }

        anchorNotNamed(decompositionLocus)
      },
      /*  "COPYLAYER" -> { //iL contains only the variable totoll not toto
          val iL = initLayer(layerSubProg2).keys.filter(isLayer(_)).filter(x => !x.startsWith("lldef") && tSymbVar.contains(x.drop(2))) //we check that the layer without ll exists
          //anchoring both lltoto and toto in memory.
          //todo faut virer def
          val llandNotll = spatialOfffsetsInt.filter(x => iL.contains(x._1) || iL.contains("ll" + x._1))
          "" + anchorNamed(llandNotll) +
            iL.toList.map(s => "copy(" + s + "," + s.drop(2) + ");").mkString("")
        },*/
      "FIELDOFFSET" -> {
        def fieldOffset(offset: Map[String, List[Int]]): String = {
          def offsetOneVar(oneVar: (String, List[Int])) = {
            val ints = oneVar._2
            var res = ints.map("" + _).mkString(",")
            res = "map.put(\"" + oneVar._1 + "\", li(" + res + "));";
            res
          }

          offset.map(offsetOneVar(_)).mkString("\n")
        }

        val spatialOfffsetsInt2 = spatialOfffsetsInt.filter(x => !x._1.startsWith("def"))
        fieldOffset(spatialOfffsetsInt2)
      },
      "FIELDLOCUS" -> {
        /**
         *
         * @param names
         * @param spatialLayer
         * @return
         */
        def fieldLocus(names: Iterable[String], spatialLayer: Map[String, InfoNbit[_]]): HashMap[String, Locus] = {
          val l: Map[String, Locus] = spatialLayer.map({ case (k, v) => k -> v.t.asInstanceOf[(Locus, Ring)]._1 })
          // .filter(x => !tSymbVar.contains(x._1)) //removes  layers defined in main
          HashMap[String, Locus]() ++ names.map((s: String) => s -> tSymbVar(s).t.asInstanceOf[(Locus, Ring)]._1) ++ l
        }
        fieldLocus(spatialOfffsetsInt.keys, layerSubProgStrict).map((kv: (String, Locus)) => //we need to know the locus, as soon as  we need to know the bit planes
          " map.put(\"" + kv._1 + "\"," + "compiler.Locus." + kv._2.javaName + ")").mkString(";\n")
      },
      "BITSIZE" -> {
        /** number of bits for non boolean variables. */
        def fieldBitSize(names: Iterable[String], spatialLayer: Map[String, InfoNbit[_]]): HashMap[String, Int] = {
          val l: Map[String, Int] = spatialLayer.filter(_._2.nb > 1).map({ case (k, v) => k -> v.nb })
            .filter(x => !tSymbVar.contains(x._1)) //removes integer layers defined in main
          HashMap[String, Int]() ++ names.filter(tSymbVar(_).nb > 1).map((s: String) => s -> tSymbVar(s).nb) ++ l
        }
        fieldBitSize(spatialOfffsetsInt.keys, layerSubProg2).map((kv: (String, Int)) =>
          " map.put(\"" + kv._1 + "\"," + kv._2 + ")").mkString(";\n") + ";"
      },
      "DISPLAYABLE" -> //theDisplayed contains two kinds of name:aux and segmented, first step should separate the segmented
        {
          if (!sameRoot(theDisplayed))
            throw (new Exception("some fields do not encode a path"+theDisplayed))
          val s = parenthesizedExp(rootOfVar(theDisplayed.head), hierarchyDisplayedField(theDisplayed)); s + "."
        },
      "INITLAYER" -> {
        val iL = initLayer(layerSubProg2)
        iL.map((kv: (String, String)) =>
          " map.put(\"" + kv._1 + "\",\"" + kv._2 + "\")").mkString(";\n") + ";\n"
      },
      "ANONYMOUSLOOP" -> {
        codeLoopAnonymous
      }
    ))

  }


  /** the sequence of calls of macros realizing the desired CA computation,
   *
   * @return the calls, plus a map called "decompositionLocus", which for each locus, and each group of memory plane,
   *         associates a number identifying an array of bit planes, used in the program.
   *         plus the set of  Displayed fields, which are simply arguments of calls to show */
  def javaOfTheCallInTheMain(): (List[String], Map[Locus, Map[List[Int], Int]], Set[String]) = {
    var lastCallCode: String = null //used to avoid generating many copy or many memo
    /** names of displayed variables,  updated as a side effect when generating the call Codes, each time we meet a call to display */
    var theDisplayed: Set[String] = HashSet()
    var decompositionLocus: Map[Locus, Map[
      List[Int], Int]] = HashMap() ++ allLocus.map(_ -> HashMap()) //empty map for each locus
    val theCalls = dagis.visitedL.reverse.asInstanceOf[List[CallProc]] //compiled calls
    var theCallCode: List[String] = List()
    for (call <- theCalls) { //rewrite the calls, by regrouping parameters
      val paramsD: List[String] = call.exps.map(_.asInstanceOf[Read[_]].which) //names of parameters passed
      //on rajoute les layers si y en a
      val paramsR: List[String] = call.names;     val params = paramsD ::: paramsR;   var callCode = call.procName + "(" //we always put the called procedure name. we now need to add the params
      var i = 0 //counter of scalar parameter
      var paramCode: List[String] = List() //code of the param for the current considered call
      var gateCountOfCall=0
      call.procName match {
        //we first consider specific system call show, copy, memo, debug
        case "show" => val callCodeArg = radicalOfVar(call.usedVars().toList.head) //we take the radical for diminishing the number of parameters
          theDisplayed += callCodeArg //sideeffect, update theDisplayed. display has allways a single arg which is the field to be displayed
          callCode += callCodeArg //in fact we could supress calls to show. We still leave them, just so that we can check those in the compiled java.
        case "copy" => assert(paramsD.size == 1 && paramsR.size == 1) //we copy bit by bit, hence int by int.
          val pR: String = radicalOfVar(paramsR(0))
          val pD: String = if (tSymbVarSafe(paramsR(0)).t == (V(), B()))
            radicalOfVarIntComp(paramsD(0))
          else radicalOfVar(paramsD(0))
          val locuspR = tSymbVarSafe(pR).locus
          val locuspD = tSymbVarSafe(pD).locus

          if (locuspR.isTransfer && !locuspD.isTransfer)
            callCode = "broadcaast(" //6 copy from 1D array to 1Darray are turned into a call to broaadcast from 1D arrau to 2D array
          //val l: mutable.LinkedHashSet[String] = mutable.LinkedHashSet(pR, pD)
          callCode += pD + "," + pR
        case "memo" => val l: mutable.LinkedHashSet[String] = mutable.LinkedHashSet() ++ params.map(radicalOfVar(_)) //copy and memo have the same effect
          callCode += l.toList.mkString(",")
        case "bug" => val nameBug = radicalOfVar(call.exps.head.asInstanceOf[Read[_]].which) //on apelle bug avec un read, c'est obligé
          val locusBug = tSymbVar(nameBug).locus.toString.dropRight(2) //dropRight enleve les deux parenthéses
          paramCode = List(nameBug, "llbug" + locusBug, "\"" + nameBug + "\"", "bugs").reverse
        case _ => //we now consider the interesting case: a call to a real CAloop
          paramCode = List("p") //this is a method PrShift that does a preliminary shift if radius is >0yyy
        //we can reconstruct spatial types, and bit numbers directly from the effective parameters:
        // call names and expressions, no need for reflection, at the end!:
          val dataParam=call.exps.map((x)=>x.asInstanceOf[Read[_]].which)
          val resultParam=call.names
          val spatialParam= shortenedSig(dataParam:::resultParam)
          val bitSigSafe=spatialParam.map(tSymbVarSafe(_).nb)
          val spatialSigSafe=spatialParam.map(tSymbVarSafe(_).t.asInstanceOf[(Locus, Ring)])

          for ((spatialType, nbit) <- spatialSigSafe zip bitSigSafe) { //retrieve spatial type and  bitSize   of parameters.
            val locus: Locus = spatialType._1
            val density = nbit * locus.density

            if (spatialType == (V(), B())) { //we can have seedDist$2 passed to a boolV, therefore, we should transform it into seedDist[2]
              paramCode = radicalOfVarIntComp(params(i)) :: paramCode; //this is what is done by radicalOfVarIntComp
              i += 1
            }
            //until now we applied same processing wether it is a name or a heap variable
            else {
              val locusParamEf = tSymbVarSafe(radicalOfVar(params(i))).locus
              if (locus.isTransfer && !locusParamEf.isTransfer) //we have done a broacast,
              {  paramCode = "broadcaast(" + radicalOfVar(params(i)) + ")" :: paramCode;   i += density         }
              //we prooceed differently depending wether the params are mem (isheap) or name of fields
              else if (isHeap(params(i))) { //its a "mem[x]
                var indexesMem: List[Int] = List()
                for (j <- 0 until density) { //iterate over the nbit scalar parameters of the form mem[2]
                  indexesMem = adress(params(i)) :: indexesMem; i += 1
                } //builds the list of memory offset associated to the locus
                indexesMem = indexesMem.reverse
                if (!decompositionLocus(locus).contains(indexesMem)) { //check wether that array2D of memory slices has already been used
                  val newMapOfLocus = decompositionLocus(locus) + (indexesMem -> decompositionLocus(locus).size)
                  decompositionLocus = decompositionLocus + (locus -> newMapOfLocus)
                }
                paramCode = locus.shortName + (decompositionLocus(locus)(indexesMem)) :: paramCode //name of formal paramer is locus plus rank stored in decompositionLocus
              }
              else //its not  a mem
              { paramCode = radicalOfVar(params(i)) :: paramCode;        i += density       }
            }
          }
          /** see latex, from the call, retrieve the layer used from the parameter names of the already compiled macro loop */
          def allLayerFromCompiledMacro(myCall: CallProc)={
            //calcul des layers de la macro appellée
            val className="compiledMacro."+radical(myCall.procName)
            // Load the Java class
            val clazz: Class[_] = Class.forName( className)

            // Get all methods of the class
            val methods: Array[Method] = clazz.getDeclaredMethods
            // Get the first method (or whichever you're interested in)
            val methodVersion  = methods.filter(_.getName.contains(methodName( myCall.procName)))
            val method:Method=methodVersion.head
            // Get the parameters of the method
            val parameters = method.getParameters.map(_.getName)
            val paramLayers=parameters.reverse.takeWhile(Named.isLayer(_)).reverse
           // val layers: Array[AST.Layer[_]] =paramLayers.map(Layers.layers(_))
            paramLayers.toList
          }
          /** fundef if recompiled*/
          val progCalled: DataProgLoop[U] = subDataProgs.getOrElse(call.procName,null)//gets the called dataProg, we won't be able to do that, when doing modular compilation.
          // CA loops can  contain layers.
          val  allLayerSafe:List[String]= //we consider the two cases:1- prog is being recompiled, 2-prog has already been compiled
           if(progCalled!=null)//prog is being recompiled, we can use it to get the layers from the symbolTable
                  progCalled.allLayers.filter(noDollarNorHashtag(_))
           else // prog had already been compiled, we retrieve the layer using scala relection, layers are the last parameters to the macro loops.
                   allLayerFromCompiledMacro(call)
          if (allLayerSafe.nonEmpty)// CA loops can  contain layers.
            paramCode =allLayerSafe.toList ++ paramCode //this portion is not suppressed because access to localProg is still possible
          gateCountOfCall=
            if(progCalled!=null)
              progCalled.gateCountMacroLoop// progCalled
            else dataStruc.Util.readStaticField("compiledMacro."+radical( call.procName) ,
              methodName(call.procName)+"GateCount").asInstanceOf[Int]//we need to read a static  "slopDelta_3_1_2_1_1GateCount"  in class "compiledMacro.grad"
      }
      callCode += paramCode.reverse.mkString(",") + ");"
      //had the gateCount as a comment
      if(gateCountOfCall!=0) {
         callCode+="// "+ gateCountOfCall + " gate"
        totalGateCount+=gateCountOfCall
      }
      if (!callCode.equals(lastCallCode) && !call.locus.equals("show"))
        theCallCode = callCode :: theCallCode //in case of copy or memo of integer, several times the same call code will be generated
      lastCallCode = callCode //in which  case we keep only the first one by ignoring the following
    }
    (theCallCode, decompositionLocus, theDisplayed)
  }
}
