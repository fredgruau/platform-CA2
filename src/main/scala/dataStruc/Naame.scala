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
    private def capitalizeFirst(s: String): String = ("" + s.charAt(0)).toUpperCase + s.substring(1).toLowerCase

       def setName(spatialFieldToBeNamed: Named, fieldName: String)=
      Named.OkToUseForName(fieldName) &&
        spatialFieldToBeNamed.name == null ||
        spatialFieldToBeNamed.name != null &&
          nbCap(spatialFieldToBeNamed.name) > nbCap(fieldName) &&
          !((spatialFieldToBeNamed.isInstanceOf[AST.Fundef[_]]))
    /**
     * for hashtable, name = connteneur name + hashtablename + "yyy*+ the key name.
     *
     * @param conteneur     all the layers starting from the top most
     * @param conteneurName the current accumulated name
     *
     */
    def setAllName(conteneur: Named, newName: String): Unit = {
    conteneur match{
      case m:HashMap[_, _]=>for ((key, value) <- m) {
        val suffix: String = key match {
          case n: Named => n.name
          case i: Int => "" + i
          case _ => null
        }
        if (suffix != null) value match {
          case v: Named => setAllName(v, newName + "yyy" + suffix)
        }
      }
      case _ =>
        val setable = setName(conteneur, newName)
        if (setable) {
          conteneur.setName(newName)
          // setFieldValue(conteneur, "name", newName)
          //if (setable || Set("root", "rootagent", "rootis").contains(newName)) {
          //  val correctNewName=  if(Set("root", "rootagent", "rootis").contains(newName)) conteneur.name else newName
          if (conteneur.isInstanceOf[BranchNamed]) { //we traverse the fields that can be reached from the root of naming
            val fields: Seq[(String, Any)] = getAllFieldValues(conteneur)
            val fieldsWithName = fields.filter(_._2.isInstanceOf[Named])
            fieldsWithName.foreach { case (name, value) =>
              //println(s"$name: $value")
              value match {
                case t: Named => setAllName(t, newName + capitalizeFirst(name))
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

    /*def mainOK(args: Array[String]): Unit = {

      class MyClassMember{
        val subField="subfield"
      }
      trait MyTrait {
        self:MyClassMember=>
        val traitField: String = "Trait Field"+subField
        var naame: String = "rr"
      }

      class SuperClass {
        val superField: Int = 42
      }
      class MyClas
      class MyClass extends SuperClass  {
        var mutableField: String = "Initial"
        val member:MyClassMember=new MyClassMember with MyTrait {}
      }

      // Création d'une instance de MyClass
      val myInstance = new MyClass

      // Modification du champ mutable dans le trait
      //setFieldValue(myInstance, "traitFieldMutable", "tt")

      // Récupération des champs et affichage des valeurs
      val fields: Seq[(String, Any)] = Naame.getAllFieldValues(myInstance)
      fields.foreach { case (name, value) =>
        println(s"$name: $value")
        value match {
          case t:MyTrait =>  t.setName("tttt")
          case _ =>
        }
      }

      // Vérification finale de la valeur du champ
      println(s"Nouvelle valeur de traitFieldMutable: ${myInstance.member.asInstanceOf[MyTrait].naame}")
    }

    def mainOld(args: Array[String]): Unit = {

      class MyClassMember extends MyTrait {
        val subField="subfield"
      }
      trait MyTrait {
        self:MyClassMember=>
        val traitField: String = "Trait Field"+subField
        var naame: String = "rr"
      }

      class SuperClass {
        val superField: Int = 42
      }
      class MyClas
      class MyClass extends SuperClass  {
        var mutableField: String = "Initial"
        val member:MyClassMember=new MyClassMember
      }

      // Création d'une instance de MyClass
      val myInstance = new MyClass

      // Modification du champ mutable dans le trait
      //setFieldValue(myInstance, "traitFieldMutable", "tt")

      // Récupération des champs et affichage des valeurs
      val fields: Seq[(String, Any)] = getAllFieldValues(myInstance)
      fields.foreach { case (name, value) =>
        println(s"$name: $value")
        value match {
          case t:MyTrait =>  setFieldValue(t, "naame", "tttt")
          case _ =>
        }
      }

      // Vérification finale de la valeur du champ
      println(s"Nouvelle valeur de traitFieldMutable: ${myInstance.member.asInstanceOf[MyTrait].naame}")
    }

    def main2(args: Array[String]): Unit = {
      trait MyTrait  {
        val traitField: String = "Trait Field"
      }

      class SuperClass {
        val superField: Int = 42
        val subClass45=new Leave with MyTrait with Named
      }
      class MyClassMember extends SuperClass
      class Leave
      class MyClass extends SuperClass  {
        var mutableField: String = "Initial"
        val subClass= new MyClassMember with MyTrait with Named
      }

      // Création d'une instance de MyClass
      val myInstance = new MyClass with Named
     // setAllName(myInstance,"raaa")
      // Modification du champ mutable dans le trait
      // setFieldValue(myInstance, "naame", "tt")

      // Récupération des champs et affichage des valeurs



      val fields: Seq[(String, Any)] = getAllFieldValues(myInstance)
      fields.foreach { case (name, value) =>
        println(s"$name: $value")
        value match {
          case t:MyTrait =>  setFieldValue(t, "naame", "tt")
          case _ =>
        }
      }

      // Vérification finale de la valeur du champ
      println(s"Nououvelle valeur de traitFieldMutable: ${myInstance.subClass.name}")
    }*/
  }

