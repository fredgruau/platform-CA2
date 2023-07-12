package compiler

import compiler.AST.Read
import compiler.Circuit.TabSymb
import compiler.DataProgLoop2.{fatherOfVar, indexOfLastUpperCase, radicalOfVar, removeAfterChar, shortenedSig}
import compiler.Instr.deployInt
import compiler.Locus.allLocus
import dataStruc.Named

import java.util.regex.Pattern
import scala.::
import scala.collection.convert.ImplicitConversions.`collection asJava`
import scala.collection.{Map, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import scala.xml.Elem

/** contains the code needed to produce the final java code */
trait ProduceJava[U <: InfoNbit[_]] {
  self: DataProgLoop[U] =>
  def javaCode: String = { //we need to generate spatial signature for macros before we can adress the main.
    val loops: Map[String, DataProgLoop[U]] = allCAloop
    val codeLoops: String = loops.map { case (k, v) => v.asInstanceOf[ProduceJava[U]].javaCodeCAloop(k) }.mkString("\n")

    def sptyp(st: Tuple2[String, DataProgLoop[U]]) = (st._1, st._2.spatialSig)

    def nbittyp(st: Tuple2[String, DataProgLoop[U]]) = (st._1, st._2.nbitSig)

    val spatialTypeParamLoops: Map[String, List[(Locus, Ring)]] = loops.map(sptyp(_)) //
    val nbitTypeParamLoops: Map[String, List[Int]] = loops.map(nbittyp(_))
    val codeMain: String = javaCodeMain(spatialTypeParamLoops, nbitTypeParamLoops)
    codeLoops + codeMain
  }

  /** Produce the code to inintialize 1D array from 2D arrays */
  def anchorParam(shortened: List[String], original: List[String]): List[String] = {
    var res: List[String] = List()
    var i = 0
    for (s: String <- shortened) {
      if (isBoolV(s)) i += 1
      else {
        var j = 0
        try while (removeAfterChar(original(i), '$') == s) {
          res = original(i) + "=" + s + "[" + j + "]" :: res //ish=isE[0]
          j += 1;
          i += 1
        } catch {
          case _: IndexOutOfBoundsException =>
        }
      }
    }
    res
  }

  /** declares all the variables local to the loops, and initializes them to zero if needed */
  def declInitParam = {
    val intReg = (standaloneRegister ++ coalesced.keys) //should be declared
    val boolReg: Iterable[String] = intReg.flatMap((s: String) => deployInt(s, tSymbVarSafe(s).nb)) //intReg which have a single component are not deployed

    /** variable which are delayed must be indentified so as to be initialized */
    def isDelayed(s: String) = delayed.contains(removeAfterChar(s, '#'))

    "int " + boolReg.map((s: String) => if (isDelayed(s)) s + "=0" else s).mkString(",")
  }

  def javaCodeCAloop(nameMacro: String): String = {
    val shortSigIn = shortenedSig(paramD);
    val shortSigOut = shortenedSig(paramR)

    /** add type to parameters, either int[] or int[][],
     * one dimension is enough for spatial type boolV, two dimensions are needed for other locus */
    def javaIntArray(s: String) = (if (isBoolV(s)) ("int [] ") else ("int [][] ")) + s

    val parameters = (shortSigIn ::: shortSigOut).map(javaIntArray(_))

    replaceAll("src/main/scala/compHandCA/templateCAloop.txt", Map(
      "NAMEMACRO" -> nameMacro,
      "PARAMETERS" -> parameters.mkString(","),
      "ANCHORPARAM" -> (anchorParam(shortSigIn, paramD) ::: anchorParam(shortSigOut, paramR)).reverse.mkString(","),
      "PROPAGATEFIRSTBIT" -> paramD.map((s: String) => "p.propagate4shift(" + s + ")").mkString(";"),
      "FIRSTPARAM" -> (paramD ::: paramR)(0), //There must be at least one param,
      // we need to read it so as to know the length which is the number of CA lines.
      //  "READPARAM"->paramD.map((s:String)=>s+"i"+"="+s+"[i]").mkString(";"),
      "DECLINITPARAM" -> declInitParam,
      "LOOPBODY" -> totalCode.map(_.toStringTreeInfix(tSymbVar.asInstanceOf[TabSymb[InfoType[_]]])).grouped(4).map(_.mkString(";")).mkString(";\n ")

    ))
  }

  /** number of bits for non boolean variables. */
  def fieldBitSize(names: Iterable[String]): HashMap[String, Int] =
    HashMap[String, Int]() ++ names.filter(tSymbVar(_).nb > 1).map((s: String) => s -> tSymbVar(s).nb)

  def fieldLocus(names: Iterable[String]): HashMap[String, Locus] = {
    val res = HashMap[String, Locus]() ++ names.map((s: String) => s -> tSymbVar(s).t.asInstanceOf[(Locus, Ring)]._1)
    val u = 0
    res
  }

  var mainCallCode: List[String] = null

  def javaCodeMain(spatialTypes: Map[String, List[(Locus, Ring)]], nbitType: Map[String, List[Int]]): String = {
    /** use  locus and parameter occurence order to create parameter names */
    val offfsetsInt = offsetsInt
    val (theCallCode, decompositionLocus) = theCalllCode(spatialTypes, nbitType)
    mainCallCode = theCallCode
    val l = layerXML
    System.out.println(l)
    replaceAll("src/main/scala/compHandCA/templateCA.txt", Map(
      "NAMECA" -> paramR(0).capitalize,
      "MEMWIDTH" -> ("" + mainHeapSize + "\n"), //TODO on calcule pas bien la memwidth)
      "DECLNAMED" -> ("" + DeclNamed(offfsetsInt)),
      "DECLNOTNAMED" -> ("" + declNotNamed(decompositionLocus)),
      "LISTCALL" -> theCallCode.reverse.mkString("\n"),
      "ANCHORNAMED" -> anchorNamed(offfsetsInt), //anchorNamed,
      "ANCHORNOTNAMED" -> anchorNotNamed(decompositionLocus),
      "FIELDOFFSET" -> fieldOffset(offfsetsInt),
      "FIELDLOCUS" -> fieldLocus(offfsetsInt.keys).map((kv: (String, Locus)) =>
        " map.put(\"" + kv._1 + "\"," + kv._2.javaName + ")").mkString("\n"),
      "BITSIZE" -> fieldBitSize(offfsetsInt.keys).map((kv: (String, Int)) =>
        " map.put(\"" + kv._1 + "\"," + kv._2 + ")").mkString("\n"),
    ))

  }

  /**
   * it uses the mainCallCode to get the display command
   *
   * @return keys are names of Layers, value are names of fields or Layers
   */
  def hierarchyDisplayedField: Map[String, List[String]] = {
    var res: Map[String, List[String]] = new HashMap()
    for (v <- theDispayed) {
      val f = fatherOfVar(v)
      val l = if (res.contains(f)) res(f) else List()
      res = res + (f -> (v :: l))
    }
    res
  }

  def layerXML = {
    val h = hierarchyDisplayedField
    val rootLayers: Iterable[String] = h.keys.filter(indexOfLastUpperCase(_) == -1).toSet - ""

    /** recursive traversing of hierarchy */
    def xmll(s: String): Elem = {
      <Layer>
        {s}{if (theDispayed.contains(s)) //if layer is printed, adds the field storing the former layer's value
      {
        <Field>
          {Named.lify(s)}
        </Field>
      }}{h(s).map(nameFieldorLayer => if (h.contains(nameFieldorLayer)) xmll(nameFieldorLayer) else {
        <Field>
          {nameFieldorLayer}
        </Field>
      }
      )}
      </Layer>
    }

    <layers>layers
      {rootLayers.map(nameLayer => xmll(nameLayer))}
    </layers>
  }


  /** names of displayed variables */
  var theDispayed: Set[String] = HashSet()

  def theCalllCode(spatialTypes: Map[String, List[(Locus, Ring)]], nbitType: Map[String, List[Int]]): (List[String], Map[Locus, Map[List[Int], Int]]) = {
    var decompositionLocus: Map[Locus, Map[List[Int], Int]] = HashMap() ++ allLocus.map(_ -> HashMap())
    val theCalls = dagis.visitedL.reverse.asInstanceOf[List[CallProc]]
    var theCallCode: List[String] = List()
    for (call <- theCalls) { //réecrit les calls.
      val paramsD: List[String] = call.exps.map(_.asInstanceOf[Read[_]].which)
      val paramsR: List[String] = call.names
      val params = paramsD ::: paramsR
      var i = 0 //counter of scalar parameter
      var callCode = call.procName + "(" //we now need to add the params
      var paramCode: List[String] = List()
      call.procName match {
        case "show" =>
          val callCodeArg = radicalOfVar(call.usedVars().toList.head)
          theDispayed += callCodeArg //display has allways a single arg which is the field to be displayed
          callCode += callCodeArg + ")"
        case "copy" | "memo" | "bug" => //
        case _ =>
          for ((spatialType, nbit) <- spatialTypes(call.procName) zip nbitType(call.procName)) {
            val locus: Locus = spatialType._1
            val density = nbit * locus.density
            if (spatialType == (V(), B())) {
              paramCode = params(i) :: paramCode; //same processing wether it is a name or a heap variable
              i += 1
            }
            else { //we prooceed differently depending wether the params are mem (isheap) or name
              if (isHeap(params(i))) { //its a mem
                var indexesMem: List[Int] = List()
                for (j <- 0 until density) { //iterate over the nbit scalar parameters of the form mem[2]
                  indexesMem = adress(params(i)) :: indexesMem; i += 1 //builds the list of memory offset associated to the locus
                }
                //check if that array2D of memory slices has already been used
                indexesMem = indexesMem.reverse
                if (!decompositionLocus(locus).contains(indexesMem)) {
                  val newMapOfLocus = decompositionLocus(locus) + (indexesMem -> decompositionLocus(locus).size)
                  decompositionLocus = decompositionLocus + (locus -> newMapOfLocus)
                }
                // decompositionLocus=decompositionLocus+(locus->(indexesMem::decompositionLocus(locus)))
                paramCode = "" + locus.parentheseLessToString + //the drop right removes parenthesis
                  (decompositionLocus(locus)(indexesMem)) :: paramCode //name of formal paramer is locus plus rank
              }
              else //its not  a mem
              {
                paramCode = radicalOfVar(params(i)) :: paramCode
                i += density
              }
            }
          }
      }
      callCode += paramCode.reverse.mkString(",") + ");"
      theCallCode = callCode :: theCallCode
    }
    (theCallCode, decompositionLocus)
  }
}

object DataProgLoop2 {
  def removeAfterChar(s: String, c: Char): String = if (s.contains(c)) s.substring(0, s.indexOf(c)) else s

  private def truncateBefore(s: String, p: String) = {
    if (s.indexOf(p) == -1) s else s.substring(0, s.indexOf(p))
  }

  def radicalOfVar(s: String): String = {
    truncateBefore(truncateBefore(s, "$"), "#")
  }

  def radicalOfVar2(s: String): String = {
    truncateBefore(s, "#")
  }

  def indexOfLastUpperCase(v: String) = {
    val pat = Pattern.compile("[A-Z][^A-Z]*$")
    val `match` = pat.matcher(v)
    var lastCapitalIndex = -1
    if (`match`.find) lastCapitalIndex = `match`.start
    lastCapitalIndex
  }

  /** returns the name of the layers containing var, or empty string if there is none */
  def fatherOfVar(v: String): String = {
    val i = indexOfLastUpperCase(v)
    if (i == -1) ""
    else v.substring(0, i)
  }

  def shortenedSig(param: List[String]): List[String] = {
    val res: mutable.LinkedHashSet[String] = mutable.LinkedHashSet()
    for (p <- param) res += radicalOfVar(p)
    return res.toList;
  }
}
