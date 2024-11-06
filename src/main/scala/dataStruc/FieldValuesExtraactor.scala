import scala.reflect.runtime.universe._
import scala.reflect.runtime.{currentMirror => cm}

/** used to come up with a correct reflective process, to find out for the names of the field. We keep
 * it because we may have to use if for test */
object FieldValuesExtraactor {

  def getAllFieldValues(instance: Any): Seq[(String, Any)] = {
    val instanceMirror = cm.reflect(instance)
    val instanceType = instanceMirror.symbol.toType

    // Récupère les champs de l'instance et de ses superclasses
    getFieldValuesWithSuperclasses(instanceMirror, instanceType)
  }

  private def getFieldValuesWithSuperclasses(instanceMirror: InstanceMirror, instanceType: Type): Seq[(String, Any)] = {
    // Récupère les champs de la classe actuelle
    val currentClassFields = instanceType.members.collect {
      case term: TermSymbol if term.isVal || term.isVar =>
        val fieldName = term.name.toString
        try {
          val fieldMirror = instanceMirror.reflectField(term.asTerm)
          val fieldValue = fieldMirror.get
          (fieldName, fieldValue)
        } catch {
          case e: Throwable =>
            println(s"Erreur Extraacteur lors de l'accès au champ $fieldName: ${e.getMessage}")
            (fieldName, "<inaccessible>")
        }
    }.toSeq

    // Récupère les champs des superclasses sans recréer un InstanceMirror
    val superclassFields = instanceType.baseClasses
      .filterNot(_ == instanceType.typeSymbol)
      .flatMap { superclass =>
        val superclassType = superclass.asType.toType
        superclassType.members.collect {
          case term: TermSymbol if term.isVal || term.isVar =>
            val fieldName = term.name.toString
            try {
              val fieldMirror = instanceMirror.reflectField(term.asTerm)
              val fieldValue = fieldMirror.get
              (fieldName, fieldValue)
            } catch {
              case e: Throwable =>
                println(s"Erreur extraacteur lors de l'accès au champ $fieldName: ${e.getMessage}")
                (fieldName, "<inaccessible>")
            }
        }
      }

    // Combine les champs de la classe actuelle et des superclasses
    currentClassFields ++ superclassFields
  }

  // Méthode pour modifier la valeur d'un champ mutable
  def setFieldValue(instance: Any, fieldName: String, newValue: Any): Unit = {
    val instanceMirror = cm.reflect(instance)
    val instanceType = instanceMirror.symbol.toType

    instanceType.members.collectFirst {
      case term: TermSymbol if term.isVar && term.name.toString == fieldName =>
        val fieldMirror = instanceMirror.reflectField(term)
        fieldMirror.set(newValue)
    }.getOrElse {
      println(s"Champ $fieldName non trouvé ou non mutable")
    }
  }

  class MyClassMember {
    val subField = "subfield"
  }

  trait MyTrait {
    val traitField: String = "Trait Field"
    var naame: String = "rr"
  }

  class SuperseuprClass{
    val supersuperField: Int = 4242
  }
  class SuperClass extends SuperseuprClass {
    val superField: Int = 42
  }

  class MyClass extends SuperClass {
    var mutableField: String = "Initial"
    val member: MyClassMember = new MyClassMember with MyTrait
  }

  def main(args: Array[String]): Unit = {
    // Création d'une instance de MyClass
    val myInstance = new MyClass

    // Récupération des champs et affichage des valeurs
    val fields: Seq[(String, Any)] = getAllFieldValues(myInstance)
    fields.foreach { case (name, value) =>
      println(s"$name: $value")
    }

    // Modification du champ mutable dans le trait
    setFieldValue(myInstance.member.asInstanceOf[MyTrait], "naame", "tttt")

    // Vérification finale de la valeur du champ
    println(s"Nouvelle valeur de naame: ${myInstance.member.asInstanceOf[MyTrait].naame}")
  }
}
