package compiler

import compiler.AST.Read
import compiler.Circuit.TabSymb
import compiler.DataProgLoop2.{radicalOfVar, removeAfterChar, shortenedSig}
import compiler.Instr.deployInt
import compiler.Locus.allLocus


import scala.collection.{Map, mutable}
import scala.collection.immutable.HashMap

trait ProduceJava[U <: InfoNbit[_]] {
  self: DataProgLoop[U] =>
  def javaCode: String = { //we need to generate spatial signature for macros before we can adress the main.
    val loops: Map[String, DataProgLoop[U]] = allCAloop

    val codeLoops: String = loops.map { case (k, v) => v.asInstanceOf[ProduceJava[U]].javaCodeCAloop(k) }.mkString("\n")

    def sptyp(st: Tuple2[String, DataProgLoop[U]]) = (st._1, st._2.spatialSig)

    def nbittyp(st: Tuple2[String, DataProgLoop[U]]) = (st._1, st._2.nbitSig)

    val spatialTypeParamLoops: Map[String, List[(Locus, Ring)]] = loops.map(sptyp(_))
    val nbitTypeParamLoops: Map[String, List[Int]] = loops.map(nbittyp(_))
    val codeMain: String = javaCodeMain(spatialTypeParamLoops, nbitTypeParamLoops)
    codeLoops + codeMain
  }

  def javaCodeCAloop(nameMacro: String): String = {
    val shortSigIn = shortenedSig(paramD);
    val shortSigOut = shortenedSig(paramR)

    /** add type to parameters, either int[] or int[][],
     * one dimension is enough for spatial type boolV, two dimensions are needed for other locus */
    def javaIntArray(s: String) = (if (isBoolV(s)) ("int [] ") else ("int [][] ")) + s

    val parameters = (shortSigIn ::: shortSigOut).map(javaIntArray(_))

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

    replaceAll("src/main/scala/compHandCA/templateCAloop.txt", Map(
      "NAMEMACRO" -> nameMacro,
      "PARAMETERS" -> parameters.mkString(","),
      "ANCHORPARAM" -> (anchorParam(shortSigIn, paramD) ::: anchorParam(shortSigOut, paramR)).reverse.mkString(","),
      "PROPAGATEFIRSTBIT" -> paramD.map((s: String) => "p.propagate4shift(" + s + ")").mkString(";"),
      "FIRSTPARAM" -> (paramD ::: paramR)(0), //There must be at least one param,
      // we need to read it so as to know the length which is the number of CA lines.
      //  "READPARAM"->paramD.map((s:String)=>s+"i"+"="+s+"[i]").mkString(";"),
      "DECLINITPARAM" -> {
        val intReg = (standaloneRegister ++ coalesced.keys)
        val boolReg: Iterable[String] = intReg.flatMap((s: String) => deployInt(s, tSymbVarSafe(s).nb))

        def isDelayed(s: String) = delayed.contains(removeAfterChar(s, '#'))

        "int " + boolReg.map((s: String) => if (isDelayed(s)) s + "=0" else s).mkString(",")
      },
      "LOOPBODY" -> totalCode.map(_.toStringTreeInfix(tSymbVar.asInstanceOf[TabSymb[InfoType[_]]])).grouped(4).map(_.mkString(";")).mkString(";\n ")

    ))
  }

  def javaCodeMain(spatialTypes: Map[String, List[(Locus, Ring)]], nbitType: Map[String, List[Int]]): String = {
    /** use  locus and parameter occurence order to create parameter names */
    val offfsetsInt = offsetsInt
    val (theCallCode, decompositionLocus) = theCalllCode(spatialTypes, nbitType)
    replaceAll("src/main/scala/compHandCA/templateCA.txt", Map(
      "NAMECA" -> paramR(0).capitalize,
      "MEMWIDTH" -> ("" + mainHeapSize + "\n"), //TODO on calcule pas bien la memwidth)
      "DECLNAMED" -> ("" + DeclNamed(offfsetsInt)),
      "DECLNOTNAMED" -> ("" + declNotNamed(decompositionLocus)),
      "LISTCALL" -> theCallCode.reverse.mkString("\n"),
      "ANCHORNAMED" -> anchorNamed(offfsetsInt), //anchorNamed,
      "ANCHORNOTNAMED" -> anchorNotNamed(decompositionLocus),
      "FIELDOFFSET" -> fieldOffset(offfsetsInt)))
  }

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
        case "copy" | "show" | "memo" | "bug" => //
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

  def shortenedSig(param: List[String]): List[String] = {
    val res: mutable.LinkedHashSet[String] = mutable.LinkedHashSet()
    for (p <- param) res += radicalOfVar(p)
    return res.toList;
  }
}
