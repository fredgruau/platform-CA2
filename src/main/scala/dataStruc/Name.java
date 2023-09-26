package dataStruc;

import compiler.AST;

import java.util.HashMap;
import java.util.Map;



public class Name {
	
	

  	//appel: setName((Named)progCompiled, ""); 
	//static void printableDeep(Object o, int n){ 

	static int nbCap(String s){int caps=0; for (int i=0; i<s.length(); i++)  if (Character.isUpperCase(s.charAt(i))) caps++; return caps;}

    /**
     * for hashtable, name = connteneur name + hashtablename + "yyy*+ the key name.
     *
     * @param conteneur     all the layers starting from the top most
     * @param conteneurName the current accumulated name
     */
	public static void setName(Named conteneur, String conteneurName) {		Class<?> c = conteneur.getClass();
	  do {java.lang.reflect.Field[] fs = c.getDeclaredFields();
          for (java.lang.reflect.Field f : fs) {     //we consider all fields, here we should may be limit to only layers
              Object o2 = null;
              f.setAccessible(true);
              String fieldName = f.getName(); //fieldname is the name given in the scala/java source code
	 // System.out.println(fieldName);
              try {
                  o2 = f.get(conteneur);
              } catch (IllegalArgumentException e) {
                  e.printStackTrace();
              } catch (IllegalAccessException e) {
                  e.printStackTrace();
              }
              if (o2 instanceof Named) //we found a class worth of consideration, because carrying a name, may be we should restrict ourself to layere here
                  setNameField(conteneur, conteneurName, (Named) o2, fieldName); //so we try to name o2
	    else if (o2 instanceof HashMap ) { 
		   HashMap<?,?>  m = (HashMap<?, ?>) o2;	for ( Object  a :m.entrySet())  {Object key = ((Map.Entry<?,?>) a).getKey(); Object value =  ((Map.Entry<?,?>) a).getValue();
	        if(value instanceof Named && key  instanceof Named  )  setNameField(  conteneur,  conteneurName+fieldName+"yyy" , (Named)value  , ((Named)key).name());
	        else if(value instanceof Named && key  instanceof Integer  )  setNameField(  conteneur,  conteneurName+fieldName+"yyy" , (Named)value  , ""+(key) );
                  }
              }
          }
          c = c.getSuperclass();// there might some field which are defined in ancestors, that we also need to scan
      } while (c != Object.class); // we will stop when reaching the root class
	}

	static int compteurToto = 0;

    /**
     * When a field is accessed through different path, we will try to name it through different container
     * each path give a possible name, we want to minimise the path length, wich is the number of uppercap
     *
     * @param conteneur             class instance containing the field we want to name
     * @param conteneurName         name of that class
     * @param spatialFieldToBeNamed spatial field that we try to name automatically, by appending the name of the container plus the name of the field containerName + fieldName
     * @param fieldName             name of the field in the scala/java source
     */
    public static void setNameField(Named conteneur, String conteneurName, Named spatialFieldToBeNamed ,String fieldName) {
        //System.out.println("setNameField  "+conteneurName +  " contains "+fieldName);
		if(fieldName==null) fieldName="toto"+compteurToto++; //that should not happen
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
            if (setName || fieldName == "root") //if root we need to rename its descendant, because root was given a name automatically but not its decendant
                setName(spatialFieldToBeNamed, spatialFieldToBeNamed.name()); //Recursive call that will name the subspatialFields, of the just named field
	        	 /* Boolean shown=false;//(fieldToName instanceof AST) ? ((AST)  fieldToName).shown():false;
	        	  if (shown) spatialFieldToBeNamed.addAfter( "_" );
	        	  else if (hide)  spatialFieldToBeNamed.addBefore( "_");*/
				}	} 	 }
	 


