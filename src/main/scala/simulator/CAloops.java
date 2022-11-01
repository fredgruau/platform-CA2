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
public interface CAloops {

    /**
     * @return the offset where to find the data in the CA memory, for a given field
     */
    public HashMap<String, List<Integer>> printedLayerOfset();

    /**
     * @return we need to know the locus in order to display the field at the right place
     */
    public HashMap<String, Locus> printedLayerLocus();

    /**
     * @return for integer fields, we need to knwo the bit size
     */
    public HashMap<String, Integer> printedLayerBitSize();

    /**
     * @param ts  list of parameters
     * @param <T> type of parameters
     * @return A scala List[T]
     */
    public static <T> List<T> list(T... ts) {
        List<T> result = List$.MODULE$.empty();
        for (int i = ts.length; i > 0; i--) {
            result = new $colon$colon(ts[i - 1], result);
        }
        return result;
    }
}
