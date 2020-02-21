package compiler
import scala.collection.mutable

object Named{
 private  var doNotUse =scala.collection.mutable.Set[String]()
 def doNotUseForName(s:Seq[String]): mutable.Set[String] ={doNotUse++= s}
 def OkToUseForName(s:String):Boolean= !doNotUse.contains(s);
 {doNotUseForName(List("arg","arg2"  ))}
}

trait Named {
  var name:String=_;  def setName(value: String) {name = value  }

 def addAfter(value: String) {name =  name+value  };def addBefore(value: String) {name =  value+name  }
}