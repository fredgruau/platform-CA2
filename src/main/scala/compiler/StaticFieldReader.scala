import compiler.DataProg.nameDirCompilLoops

import java.lang.reflect.Field

object StaticFieldReader2 {
  def readStaticField2(className: String, fieldName: String): Unit = {
    try {
      // Load the class by name
      val clazz: Class[_] = Class.forName(className)

      // Get the field by name
      val field: Field = clazz.getField(fieldName)

      // Ensure the field is static and public
      if (java.lang.reflect.Modifier.isStatic(field.getModifiers)) {
        // Get the value of the static field and print it
        val fieldValue: Any = field.get(null)  // `null` because it's a static field
        println(s"Value of static field $fieldName: $fieldValue")
      } else {
        println(s"Field $fieldName is not static.")
      }

    } catch {
      case e: ClassNotFoundException =>
        println(s"Class $className not found.")
      case e: NoSuchFieldException =>
        println(s"Field $fieldName not found in class $className.")
      case e: IllegalAccessException =>
        println(s"Cannot access field $fieldName in class $className.")
      case e: Exception =>
        e.printStackTrace()
    }
  }


// Usage example
def main(args: Array[String]) ={
 // nameDirCompilLoops
StaticFieldReader2.readStaticField2("compiledMacro.grad", "slopDelta_3_1_2_1_1GateCount")
}
}
/*
Explanation:
  Class.forName(className): This dynamically loads the class with the given name.
  clazz.getField(fieldName): This retrieves the public field with the given name.
field.get(null): Since the field is static, you pass null to get its value.
  The try-catch blocks handle potential exceptions like ClassNotFoundException, NoSuchFieldException, and IllegalAccessException.
*/