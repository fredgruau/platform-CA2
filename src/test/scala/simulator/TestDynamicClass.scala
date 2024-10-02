package simulator

import compiler.Locus
import dataStruc.Util.{getProg, loadClass}
import org.scalatest.{BeforeAndAfter, FunSuite}
import simulator.SimulatorUtil._

import scala.collection.JavaConverters._

class TestDynamicClass extends FunSuite with BeforeAndAfter {
  test("loadClass, getProg") {
    val cl = loadClass("compiledCA.TestCA")
    val ca = getProg(cl)
    val scalaMap: Map[String, List[Integer]] = ca.fieldOffset.asScala.toMap
    val scalaMap2: Map[String, Locus] = ca.fieldLocus.asScala.toMap
    val scalaMap3: Map[String, Integer] = ca.fieldBitSize.asScala.toMap
    println(scalaMap)
    println(scalaMap2)
    println(scalaMap3)
  }
}

