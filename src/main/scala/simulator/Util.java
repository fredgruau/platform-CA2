package simulator;

import scala.collection.immutable.$colon$colon;
import scala.collection.immutable.List;
import scala.collection.immutable.List$;

/**
 * static methods of general utility plus
 * also static variablle such as defVE which are allways used, and allways the same
 */
public class Util {
    public static int[][] defVe;
    public static int[] defe, defse, defsw, defw, defnw, defne;
    public static int[] bug;

    public static void anchorFixedInMem(int[][] m) {
        bug = m[0];
        defVe = new int[][]{m[1], m[2], m[3], m[4], m[5], m[6]};
        defe = defVe[0];
        defse = defVe[1];
        defsw = defVe[2];
        defw = defVe[3];
        defnw = defVe[4];
        defne = defVe[5];
    }

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
