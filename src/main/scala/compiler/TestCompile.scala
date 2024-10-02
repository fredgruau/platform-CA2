package compiler

import compiler.Circuit.compileJavaFiles
import dataStruc.Util.writeFile

object TestCompile {

  val path="src/main/java/compiledCA/TestGen2.java"
def generateJavaFiles()={
  val  src=" package compiledCA;public class TestGen2 { public static void main(){System.out.println(\"bonjour\");}}"
  writeFile(path,src)
}

  def main(args: Array[String]): Unit = {
    // Step 1: Generate Java files
    generateJavaFiles()

    // Step 2: Compile the generated Java files
    val sourceFiles = List(path)
    val compilationSuccess = compileJavaFiles(sourceFiles)

    // Step 3: Ensure compilation succeeded before proceeding
    if (compilationSuccess) {
      println("Compilation successful, launching the main program.")
      // Now run your main program logic
      //runMainProgram()
    } else {
      println("Compilation failed, cannot run the main program.")
    }
  }


}
