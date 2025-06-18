package dataStruc
import org.scalatest.{BeforeAndAfter, FunSuite}
class CacheTest extends  FunSuite with BeforeAndAfter{
  test("size log"){
    val c=new Cache[Int]
    for(i <- 0 to 113) {
      c.push(i)
    }
    print(c.size)
    for(i<- 0 to 35)
      println(c.pop(1))
  }
}
