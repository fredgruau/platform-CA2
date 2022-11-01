package simulator

import DynamicClassUtility.{getProg, loadClass}
import compiler.Locus
import org.scalatest.{BeforeAndAfter, FunSuite}
import scala.collection.JavaConverters._

class TestDynamicClass extends FunSuite with BeforeAndAfter {
  test("loadClass, getProg") {
    val cl = loadClass("compiledCA.TestCA")
    val ca = getProg(cl)
    val scalaMap: Map[String, List[Integer]] = ca.printedLayerOfset.asScala.toMap
    val scalaMap2: Map[String, Locus] = ca.printedLayerLocus.asScala.toMap
    val scalaMap3: Map[String, Integer] = ca.printedLayerBitSize.asScala.toMap
    println(scalaMap)
    println(scalaMap2)
    println(scalaMap3)
  }
}

