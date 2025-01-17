package dataStruc
import scala.reflect.runtime.universe._
import scala.reflect.runtime.{currentMirror => cm}
import compiler.AST

import scala.collection.mutable.HashMap

trait BranchNamed
  /**
   * Depuis la classe Circuit, explore récursivement tout les fields qui héritent de Named, ainsi
   * que leur superclasse, et leurs interfaces.
   * A chaqe fois qu'on descends suivant un field,
   * Positionne le champ name des field visité en minimisant le nombre
   * de segment de chemin.
   */
  object Naame {
    //appel: setName((Named)progCompiled, "");
    //static void printableDeep(Object o, int n){
     def nbCap(s: String): Int = {
      var caps: Int = 0
      for (i <- 0 until s.length) {
        if (Character.isUpperCase(s.charAt(i))) {
          caps += 1
        }
      }
      return caps
    }
    private def capitalizeFirst(s: String): String = if(s=="") "" else ("" + s.charAt(0)).toUpperCase + s.substring(1).toLowerCase

    def removeDot(input: String): String = {
      input.replace(".", "")
    }

    def setName(spatialFieldToBeNamed: Named, fieldName: String)=
      Named.OkToUseForName(fieldName) &&
        spatialFieldToBeNamed.name == null ||
        spatialFieldToBeNamed.name == "" ||
        spatialFieldToBeNamed.name != null &&
          nbCap(spatialFieldToBeNamed.name) > nbCap(fieldName) &&
          !((spatialFieldToBeNamed.isInstanceOf[AST.Fundef[_]]))
    /**
     * for hashtable, name = connteneur name + hashtablename + "yyy*+ the key name.
     *
     * @param conteneur     all the layers starting from the top most, or agents with syysinstr
     * @param conteneurName the current accumulated name
     *
     */
    def setAllName(conteneur: Named, newName: String): Unit = {
    conteneur match{
      case m:HashMap[_, _]=>
        for ((key, value) <- m) {
        val suffix: String = key match {
          case n: Named => n.name
          case s:String =>
            s.toLowerCase()
          case i: Int =>
            "" + i
          case _ => null
        }
        if (suffix != null) value match {
          case v: Named => setAllName(v, newName + "yyy" + suffix)
        }
      }
      /*case t:Array[_]=>  //marche pas car array ne peut pas étendre Named.
        for(i <- 0 until t.length)
          t(i) match {
            case v: Named => setAllName(v, newName + "ttt" +i)
          }*/
      case _ =>
        val setable = setName(conteneur, newName)
        if (setable) {
          if(conteneur.name!="")
            conteneur.setName(removeDot( newName)) //le name empty string est un cas spécial
          // setFieldValue(conteneur, "name", newName)
          //if (setable || Set("root", "rootagent", "rootis").contains(newName)) {
          //  val correctNewName=  if(Set("root", "rootagent", "rootis").contains(newName)) conteneur.name else newName
          if (conteneur.isInstanceOf[BranchNamed]) { //we traverse the fields that can be reached from the root of naming
            val fields: Seq[(String, Any)] = getAllFieldValues(conteneur)
            val fieldsNonRecur = fields.filter(_._2 != conteneur)
            val fieldsUnique=fieldsNonRecur.toSet.toList //on enleve les doublons, poil au fion
            val fieldsWithName =fieldsUnique.filter(_._2.isInstanceOf[Named])


            val fieldHasMap=fields.filter(_._2.isInstanceOf[HashMap[_,_]])

            fieldsWithName.foreach { case (name, value) =>
              //println(s"$name: $value")
              value match {
                case t: Named =>
                  val nameOublieN=
                    if(t.name=="")
                       ""
                    else name
                  setAllName(t, newName + removeDot( capitalizeFirst(nameOublieN)))
                case _ =>
              }

            }
          }
        }
      }
    }

      def getAllFieldValues(instance: Any): Seq[(String, Any)] = {
        val instanceMirror = cm.reflect(instance)
        val instanceType = instanceMirror.symbol.toType

        // Récupère les champs de l'instance et de ses superclasses
        getFieldValuesWithSuperclasses(instanceMirror, instanceType)
      }



    private def getFieldValuesWithSuperclasses(instanceMirror: InstanceMirror, instanceType: Type): Seq[(String, Any)] = {
      val currentClassFields = instanceType.members.collect {
        case term: TermSymbol if term.isVal || term.isVar =>
          val fieldName = term.name.toString.trim
          try {
            val fieldMirror = instanceMirror.reflectField(term.asTerm)
            val fieldValue = fieldMirror.get
            (fieldName, fieldValue)
          } catch {
            case _: Throwable =>
              // Si le champ direct est inaccessible, cherche un accesseur `def` avec le même nom
              try {
                val methodSymbol = instanceType.member(TermName(fieldName)).asMethod
                val methodMirror = instanceMirror.reflectMethod(methodSymbol)
                (fieldName, methodMirror.apply())
              } catch {
                case e: Throwable =>
                  println(s"Erreur pas super class, lors de l'accès au champ ou méthode $fieldName: ${e.getMessage}")
                  (fieldName, "<inaccessible>")
              }
          }
      }.toSeq

      val superclassFields = instanceType.baseClasses
        .filterNot(_ == instanceType.typeSymbol)
        .flatMap { superclass =>
          val superclassType = superclass.asType.toType
          superclassType.members.collect {
            case term: TermSymbol if term.isVal || term.isVar && !term.name.toString.trim.endsWith("_$eq")=> //we filter out access to the var setter
              val fieldName = term.name.toString.trim
              try {
                val fieldMirror = instanceMirror.reflectField(term.asTerm)
                val fieldValue = fieldMirror.get
                (fieldName, fieldValue)
              } catch {
                case _: Throwable =>
                  // Cherche un accesseur `def` si le champ est inaccessible
                  try {
                    val methodSymbol = superclassType.member(TermName(fieldName)).asMethod
                    val methodMirror = instanceMirror.reflectMethod(methodSymbol)
                    (fieldName, methodMirror.apply())
                  } catch {
                    case e: Throwable =>
                      println(s"Erreur Super Class lors de l'accès au champ ou méthode $fieldName: ${e.getMessage}")
                      (fieldName, "<inaccessible>")
                  }
              }
          }
        }
      currentClassFields ++ superclassFields
    }

/** programme de test */
      def main(args: Array[String]): Unit = {

      class MyClassSubmember extends Named {
        val subField="submemberfield"
      }

      class MyClassMember extends BranchNamed with Named {
        val subField="subfield"
        val subMember=new MyClassSubmember
      }


      class SuperClass {
        val superField: Int = 42
      }
      class MyClas
      class MyClass extends SuperClass with BranchNamed with Named {
        var mutableField: String = "Initial"
        val member:MyClassMember=new MyClassMember
      }

      // Création d'une instance de MyClass
      val myInstance = new MyClass
       setAllName(myInstance,"racine")

      // Vérification finale de la valeur du champ
      println(s"Nouvelle valeur du name de member: ${myInstance.member.asInstanceOf[Named].name}")
    }

  }

