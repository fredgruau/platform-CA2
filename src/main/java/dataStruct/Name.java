/*
package dataStruct;

import compiler.AST;
import compiler.S;
import dataStruc.Named;
import scala.Tuple2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;




*/
/**
 * Depuis la classe Circuit, explore récursivement tout les fields qui héritent de Named, ainsi
 * que leur superclasse, et leurs interfaces.
 * A chaqe fois qu'on descends suivant un field,
 * Positionne le champ name des field visité en minimisant le nombre
 * de segment de chemin.
 *//*

public class Name {
	
	

  	//appel: setName((Named)progCompiled, ""); 
	//static void printableDeep(Object o, int n){ 

	static int nbCap(String s){int caps=0; for (int i=0; i<s.length(); i++)  if (Character.isUpperCase(s.charAt(i))) caps++; return caps;}
    public static void setAllName2(Named conteneur, String conteneurName) {
        Class<?> c = conteneur.getClass();
        java.lang.reflect.Field[] fs = c.getDeclaredFields();
        for (java.lang.reflect.Field f : fs) {
        }
    }
    */
/**
     * for hashtable, name = connteneur name + hashtablename + "yyy*+ the key name.
     *
     * @param conteneur     all the layers starting from the top most
     * @param conteneurName the current accumulated name
     *
     *//*

	public static void setAllName(Named conteneur, String conteneurName) {
        Class<?> c = conteneur.getClass();
        setAllNameRec(conteneur, c, conteneurName);
    }
    public static void setAllNameRecOld(Named conteneur,Class<?> c,String conteneurName ){
	  do {java.lang.reflect.Field[] fs = c.getDeclaredFields();
          for (java.lang.reflect.Field f : fs) {     //we consider all fields, here we should may be limit to only layers
              Object o2 = null;
              f.setAccessible(true);
              String fieldName = f.getName(); //fieldname is the name given in the scala/java source code
	       System.out.println("conteneur: "+ conteneur.name()+ ", class: "+c.getName()+", conteneurName:"+conteneurName+",field: "+fieldName);
           try {
                  o2 = f.get(conteneur);
              } catch (IllegalArgumentException e) {
                  e.printStackTrace();
              } catch (IllegalAccessException e) {
                  e.printStackTrace();
              }
              if (o2 instanceof Named) //we found a class worth of consideration, because carrying a name, may be we should restrict ourself to layers here
                  setNameField(conteneur, conteneurName, (Named) o2, fieldName); //so we try to name o2
	    else if (o2 instanceof HashMap ) {  //we consider also hashmap, it is usefull for naming consecutive flip, for example
		   HashMap<?,?>  m = (HashMap<?, ?>) o2;	for ( Object  a :m.entrySet())  {Object key = ((Map.Entry<?,?>) a).getKey(); Object value =  ((Map.Entry<?,?>) a).getValue();
	        if(value instanceof Named && key  instanceof Named  )
                setNameField(  conteneur,  conteneurName+fieldName+"yyy" , (Named)value  , ((Named)key).name());
	        else if(value instanceof Named && key  instanceof Integer  )
                setNameField(  conteneur, conteneurName+ capitalizeFirst(fieldName+"yyy" ), (Named)value  , ""+(key) );
                  }
              }
          }

         */
/* // Récupérer les interfaces implémentées par la classe
          Class<?>[] interfaces = c.getInterfaces();
          // Afficher les interfaces
          System.out.println("Interfaces implémentées par " + c.getName() + " :");
          for(Class interfaceClass:interfaces){
              System.out.println(interfaceClass.getName()      );
              setAllNameRec(conteneur,interfaceClass, conteneurName );//recursive call
          }*//*




          c = c.getSuperclass();// there might be some field which are defined in ancestors, that we also need to scan
      } while (c != Object.class && c!= null); // we will stop when reaching the root class
	}

    public static void setAllNameRec(Named conteneur,Class<?> c,String conteneurName ){
        List<Tuple2<String, Object>> fieldInstances = ScalaReflectionHelper.getAllFieldInstances(conteneur);
        System.out.println("Instances des champs de l'objet : " + fieldInstances);
        for(Tuple2<String, Object> t:fieldInstances ){
            if(t._2 instanceof Named)
                setNameField(conteneur, conteneurName, (Named) t._2, t._1);}
    }

    static int compteurToto = 0;
     public static String capitalizeFirst(String s){
         return ((""+s.charAt(0)).toUpperCase() + s.substring(1).toLowerCase());
     }
    */
/**
     * When a field is accessed through different path, we will try to name it through different container
     * each path give a possible name, we want to minimise the path length, wich is the number of uppercap
     *
     * @param conteneur             class instance containing the field we want to name
     * @param conteneurName         name of that class
     * @param spatialFieldToBeNamed spatial field that we try to name automatically, by appending the name of the container plus the name of the field containerName + fieldName
     * @param fieldName             name of the field in the scala/java source
     *//*

    public static void setNameField(Named conteneur, String conteneurName, Named spatialFieldToBeNamed ,String fieldName) {
        //System.out.println("setNameField  "+conteneurName +  " contains "+fieldName);
		if(fieldName==null)
            fieldName="toto"+compteurToto++; //that should not happen
		Boolean hide = false;//(fieldToName instanceof AST) ? ((AST) fieldToName).hidden():true;

        if (fieldName.charAt(0)=='_') 	{fieldName=fieldName.substring(1);
            hide = true;
        }//probably obsolete
        if (Named.OkToUseForName(fieldName)) {
            if (!conteneurName.equals("")) //if not the root container in which case field would be the root
                fieldName = ("" + fieldName.charAt(0)).toUpperCase() + fieldName.substring(1).toLowerCase();//transforming field name into a path segment
            //if(fieldToName.ignoreForName)  	fieldName="";
            //We will change the name if new proposed name is shorter in the hierarchy, the number of path segments correspond to the number of upperCap
            boolean setName = spatialFieldToBeNamed.name() == null || spatialFieldToBeNamed.name() != null &&
                    nbCap(spatialFieldToBeNamed.name()) > nbCap(conteneurName + fieldName)
                    && !(spatialFieldToBeNamed instanceof AST.Fundef);
            if (setName)
                spatialFieldToBeNamed.setName(conteneurName + fieldName); //we will need to rename its desdendant
            if (setName || fieldName == "root" || fieldName == "rootagent"|| fieldName == "rootis") //if root we need to rename its descendant, because root was given a name automatically but not its decendant
                setAllName(spatialFieldToBeNamed, spatialFieldToBeNamed.name()); //Recursive call that will name the subspatialFields, of the just named field
	        	 */
/* Boolean shown=false;//(fieldToName instanceof AST) ? ((AST)  fieldToName).shown():false;
	        	  if (shown) spatialFieldToBeNamed.addAfter( "_" );
	        	  else if (hide)  spatialFieldToBeNamed.addBefore( "_");*//*

				}	} 	 }




	 


*/
