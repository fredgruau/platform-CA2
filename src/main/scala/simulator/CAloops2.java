package simulator;

import compiler.Locus;
import scala.collection.immutable.$colon$colon;
import scala.collection.immutable.List;
import scala.collection.immutable.List$;

import java.util.HashMap;

/**
 * method that  should be produced by the compiler in order to describe a CA
 * on top of the program itself, in java, we find information needed to display
 */
public interface CAloops2 {

    // void theLoops(int[][] mem, PrShift p);

    /**
     * applies a set of loops realizing one iteration on the CA.
     */
    void theLoops(PrShift p);


    /**
     * @return the layer for which an init method is programmed in the medium
     * all layers which starts by def have a similar method of being initalized, so as
     * to indicate wether a neighbor in a given direction is or is not defined.
     * This method is called "def" and defE,defF, defVe are initialized with def,
     * because it is mentionned as such in the paramCA xml file associated to grow CA.
     */
    public List<String> directInit();

    /**
     * first dimension of the memory
     */
    public int CAmemWidth();

    /**
     * @return the offset where to find the data in the CA memory, for a given field
     */
    public void anchorFieldInMem(int[][] m);

    public HashMap<String, List<Integer>> fieldOffset();

    /**
     * @return locus of fields, used for displaying or initializing
     */
    public HashMap<String, Locus> fieldLocus();

    /**
     * @return for integer fields, we need to knwo the bit size
     */
    public HashMap<String, Integer> fieldBitSize();


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

    public static List<Integer> li(int... ts) {
        return list(toInts(ts));
    }
}
