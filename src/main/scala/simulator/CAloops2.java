package simulator;

import compiler.Locus;
import scala.collection.immutable.$colon$colon;
import scala.collection.immutable.List;
import scala.collection.immutable.List$;

import java.util.ArrayList;
import java.util.HashMap;

/**
 * contains all the methods that  should be produced by the compiler in order to describe a CA
 * it is the program itself, in java, but also much more information,
 * for example information needed for memorization, for display
 */
public interface CAloops2 {


    /**
     *
     * @param p prepare for a loop of radius one by doing the necessary shift
     * @return names of detected bug, if any
     * applies a set of loops realizing one iteration on the CA.
     */

    ArrayList<String> theLoops(PrShift p, int[][] m);



    /**
     * first dimension of the memory
     */
    public int CAmemWidth();

    /**
     * @return the offset where to find the data in the CA memory, for a given field
     */
    //public void anchorFieldInMem(int[][] m);

    public HashMap<String, List<Integer>> fieldOffset();

    public HashMap<String, List<String>> textOfFields();


    /**
     * @return locus of fields, used for displaying or initializing
     */
    public HashMap<String, Locus> fieldLocus();

    /**
     * @return for integer fields, we need to knwo the bit size
     */

    public HashMap<String, Integer> fieldBitSize();

    /**
     * @return how to init each layer
     */
    public HashMap<String, String> init();

    int[] arr = {1, 2, 3, 4, 5};

    // programme pour convertir un array d'entiers primitifs en liste d'entiers
    public static Integer[] toInts(int[] arr) {
        Integer[] arri = new Integer[arr.length];
        int i = 0;
        for (int v : arr) arri[i++] = v;
        return arri;
    }
         /*   List<Integer> list = Arrays.stream(arr)        // IntStream
                    .boxed()          // Stream<Integer>
                    .collect(Collectors.toList());
        return list}*/

    /**
     * @param ts  list of parameters
     * @param <T> type of parameters
     * @return A scala List[T] translating a java List.
     */
    public static <T> List<T> list(T... ts) {
        List<T> result = (List<T>) List$.MODULE$.empty();
        for (int i = ts.length; i > 0; i--) {
            result = new $colon$colon(ts[i - 1], result);
        }
        return result;
    }
/*

    public static List<Integer> li(int... ts) {
        return list(toInts(ts));
    }
*/

    String displayableLayerHierarchy();

    public int gateCount();
}
