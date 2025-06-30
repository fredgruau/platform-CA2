package simulator;

import scala.collection.immutable.$colon$colon;
import scala.collection.immutable.List;
import scala.collection.immutable.List$;

import java.util.ArrayList;
import java.util.HashSet;

/**
 * static methods of general utility plus
 * also static variablle such as defVE which are allways used, and allways the same
 */
public class Util {



    /**
     * @param shouldBeZero should allways be false
     * @param bugV         accumulates vertic bug
     * @param bugName      identifies the bug
     * @param bugs         stores detected bug
     *                     records bugName in bugs, should toBeTested be not null
     *                     updates the bugV field whish shows all the bug,
     */
    public static void bug(int[] shouldBeZero, int[] bugV, String bugName, ArrayList<String> bugs) {
        boolean bug = false;
        for (int i = 0; i < shouldBeZero.length; i++) {
            bug = bug || shouldBeZero[i] != 0;
            bugV[i] |= shouldBeZero[i];
        }
        if (bug) bugs.add(bugName);
    }

    /**
     * @param test    2D arrays, should allways be false, otherwise there is a bug
     * @param bugE    accumulates edge or face or transfer bug, 2D arrays
     * @param bugName identifies the bug
     * @param bugs    stores detected bug
     */
    public static boolean bug(int[][] test, int[][] bugE, String bugName, ArrayList<String> bugs) {
        boolean bug = false;
        for (int i = 2; i < test.length-1; i++) //on zappe les deux premieres et la derniére ligne, car il arrive que y ais des "reste de miroir brisés " la dessus.
            for (int j = 0; j < test[0].length; j++) {
                //todo we have to do a more precise test, to eliminate border effect on first and last line, first and last column.
                bug = bug || test[i][j] != 0;
                bugE[i][j] |= test[i][j];
            }
        if (bug)
            bugs.add(bugName);
        return bug;
    }

/*

   public static int[][] defVe;
    public static int[] defe, defse, defsw, defw, defnw, defne;
    public static int[] bug;
*/

    /**
     * @param src field to be displayed
     */
    public static void show(int[] src) {
    }
    public static void show(int[][] src) {
    }


    /**
     * System call
     * @param src source array
     * @param dest destination array toward which we duplicate
     */
    public static void copy(int[] src, int[] dest) {
        assert (src.length == dest.length);
        System.arraycopy(src, 0, dest, 0, src.length);
    }

    /** reset to zero the line that are initialized by miror, but not covered by loop
     * oboqlete, we reprogram the bug detection in order to zap the first two and the last line. */
    public static void resetArrayFirst2LastLineToZero(int[][] a) {
            for (int j = 0; j < a[0].length; j++) {
                a[0][j] = 0;a[1][j] = 0;
                a[a.length-1][j] = 0;
            }}
    /** reset everything to zero, not necessary*/
    public static void resetArrayToZero(int[][] array) {
        for (int i = 0; i < array.length; i++) {
            for (int j = 0; j < array[i].length; j++) {
                array[i][j] = 0;}}}

    /**
     * System call
     *
     * @param src  source array
     * @param dest destination array toward which we duplicate
     */
    public static void copyBasic(int[][] src, int[][] dest) {
        assert (src.length == dest.length);
        for (int i = 0; i < src.length; i++)
            copy(src[i], dest[i]);
    }

    public static void copy(int[][] src, int[][] dest) {
        assert (src.length <= dest.length);
        assert (dest.length % src.length == 0);
        int rapport = dest.length / src.length;
        for (int i = 0; i < src.length; i++)
            for (int j = 0; j < rapport; j++)
                copy(src[i], dest[i * rapport + j]);
    }
    /** use for compiling the elt operator.*/
    public static void copy(int[][] src, int component, int[][] dest) {
        assert (src.length >= dest.length);
        assert (src.length % dest.length == 0);
        int rapport = src.length / dest.length;
        for (int i = 0; i < dest.length; i++)
            copy(src[i*rapport +component], dest[i]);
    }

    /**
     *
     * @param src
     * @param index
     * @param dest
     */
    public static void proj(int[][] src, int index, int[][] dest) {
        assert (src.length >= dest.length);
        assert (src.length % dest.length == 0);
        int rapport = src.length / dest.length;
        for (int i = 0; i < dest.length; i++)
            copy(src[i +index*rapport], dest[i]);
    }

    /** use for compiling the elt operator.*/
    public static int[][] copy(int[][] src, int component,int scalarDensitySrc) {
        assert (src.length % scalarDensitySrc == 0);
        int [][] res=new int[src.length/scalarDensitySrc][src[0].length];
        for (int i = 0; i < res.length; i++)
            copy(src[i*scalarDensitySrc +component], res[i]);
        return res;
    }



    /**
     * when doing a braodcast from E or F we need to double , resp triple the array size
     */
    public static int[][] broadcaast(int[][] src) {
        int rapport = 6 / src.length;  //todo, on utilise la nombre de composante pour identifier le locus. Mais un IntE(2) a 6 composantes, et ce n'est pas un transfer.
        assert (rapport == 2 || rapport == 3 || rapport == 1);
        if (rapport == 1) return src;
        int dest[][] = new int[rapport * src.length][src[0].length];
        for (int i = 0; i < src.length; i++)
            for (int j = 0; j < rapport; j++)
                copy(src[i], dest[i * rapport + j]);
        return dest;
    }
    /** we now explicitely pass the number of bits.
     * this version takes the two aspect into account: number of bits, and density rapport */

    public static int[][] broadcaast33(int nbit,int rapport, int[][] src) {
        if (rapport == 1) return src; //nothing to do if densities are equal
        assert(rapport==2 || rapport == 3 || rapport == 6);
        assert(src.length % nbit == 0);
        int dest[][] = new int[rapport * src.length][src[0].length]; //interpret rapport
        for (int i = 0; i < src.length/nbit; i++) //parcourt src
            for (int j = 0; j < rapport; j++) //parcours les 2,3, ou 6 voisins vers lesquels on broadcast
                for (int k = 0; k < nbit; k++) //parcours les 2,3, ou 6 voisins vers lesquels on broadcast
                    copy(src[i*nbit+k], dest[i *nbit * rapport + j*nbit+ k]);
        return dest;
    }

    /**we  pass the rapport as a parameter,
     * this version works for boolean, for boolE broadcasterd to boolEv for example
     * a given component is reproduced.
     * hypothese de travail le resultat est toujours transfer. faut qu'on sache le nombre de bit.*/
    public static int[][] broadcaastVersion1(int rapport,int[][] src) {
        if (rapport == 1) return src;
        int dest[][] = new int[rapport * src.length][src[0].length];
        for (int i = 0; i < src.length; i++) //parcourt les bits a dupliquer
            for (int j = 0; j < rapport; j++) //parcours les 6 voisins
                copy(src[i], dest[i * rapport + j]);
        return dest;
    }

    /**we need to pass the rapport as a parameter, when using uint */
    public static int[][] broadcaastVersion2Int(int rapport,int[][] src) {
        if (rapport == 1) return src;
        int dest[][] = new int[rapport * src.length][src[0].length];
        for (int i = 0; i < src.length; i++) //parcourt les bits a dupliquer
            for (int j = 0; j < rapport; j++) //parcours les 6 voisins
                copy(src[i], dest[i  + j*src.length]);
        return dest;
    }
    /**we need to pass the rapport as a parameter, when using uint */
    public static int[][] broadcaast(int rapport,int[][] src) {
        //hypothese de travail le resultat est toujours transfer. faut qu'on sache le nombre de bit.
        return(broadcaastVersion1(rapport,src));
    }



    public static void broadcaast(int[] src, int[][] dest) {
        for (int j = 0; j < dest.length; j++)
            copy(src, dest[j]);
    }

    /**
     *
     * @param src represent a boolV
     * @return Represent a transfer field obtained by 6 ref to the boolV, thus achieving the broadcasting , without allocation memory, yeah
     */
    public static int[][] broadcaaast(int[] src) {
        int dest[][] = new int[6][src.length];
        for (int j = 0; j < dest.length; j++)
            copy(src, dest[j]);
        return dest;
    }

    /**
     * used to broadcast an Int field, such as a distance
     */
    public static void broadcaast(int[][] src, int[][] dest) {
        int arity = dest.length / src.length;
        for (int j = 0; j < arity; j++)
            for (int i = 0; i < src.length; i++)
                copy(src[i], dest[j * src.length + i]);
    }
    /**
     * used to broadcast an IntE field, such as a distance to an int Transfer field
     */
    public static void broadcaast(int rapport, int[][] src, int[][] dest) {
        int arity = dest.length / src.length; //
        int nbit= dest.length/6;

        for (int i = 0; i < nbit; i++)
                for (int j = 0; j < src.length; j++)
                    for (int k = 0; k < rapport; k++)
                copy(src[i+j*nbit], dest[i+j*rapport*nbit+k*nbit]);
    }
    /**
     * System call used to update layers, same as copy, we use demo for clarity
     *
     * @param src  source array
     * @param dest destination array toward which we duplicate
     */
    public static void memo(int[] src, int[] dest) {
        assert (src.length == dest.length);
        System.arraycopy(src, 0, dest, 0, src.length);
    }

    /**
     * System call used to update layers, same as copy, we use demo for clarity
     *
     * @param src  source array
     * @param dest destination array toward which we duplicate
     */
    public static void memo(int[][] src, int[][] dest) {
        assert (src.length == dest.length);
        for (int i = 0; i < src.length; i++)
            copy(src[i], dest[i]);
    }

/*    public static void anchorFixedInMem(int[][] m) {
        bug = m[0];
        defVe = new int[][]{m[1], m[2], m[3], m[4], m[5], m[6]};
        defe = defVe[0];
        defse = defVe[1];
        defsw = defVe[2];
        defw = defVe[3];
        defnw = defVe[4];
        defne = defVe[5];
    }*/

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
    public static List<String> ls(String... ts) {
        return list(ts);
    }
}
