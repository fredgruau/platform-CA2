package compiledCA;

import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops;

import java.util.HashMap;


/**
 * This illustrate an example of the files that should be produced by the compiler in order to describe a CA
 */
public final class GrowCA implements CAloops {
    @Override
    public HashMap<String, List<Integer>> printedLayerOfset() {
        // of string and integer type
        HashMap<String, List<Integer>> map = new HashMap<>();
        map.put("grow", CAloops.list(new Integer(0)));
        return (map);
    }

    @Override
    public HashMap<String, Locus> printedLayerLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("grow", Locus.locusV());
        return (map);
    }

    @Override
    public HashMap<String, Integer> printedLayerBitSize() {
        HashMap<String, Integer> map = new HashMap<>();
        return (map);
    }
}
