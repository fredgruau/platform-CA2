package simulator

object DynamicClassUtility {

  /**
   *
   * @param path where to find a compiledCA     */
  def loadClass(path: String): Class[CAloops] = {
    var res: Class[CAloops] = null;
    try {
      res = Class.forName(path).asInstanceOf[Class[CAloops]];
    }
    catch {
      case e: ClassNotFoundException =>
        System.out.println("la classe " + path + " n'existe même pas");
    }
    return res;
  }

  def getProg(progClass: Class[CAloops]): CAloops = {
    var res: CAloops = null
    try res = progClass.newInstance
    catch {
      case e: InstantiationException =>
        e.printStackTrace()
      case e: IllegalAccessException =>
        e.printStackTrace()
    }
    res
  }
}
