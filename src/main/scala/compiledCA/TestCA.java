package compiledCA;

import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops;

import java.util.HashMap;


/**
 * This illustrate an example of the files that should be produced by the compiler in order to describe a CA
 */
public final class TestCA implements CAloops {

    @Override
    public HashMap<String, List<Integer>> printedLayerOfset() {
        HashMap<String, List<Integer>> map = new HashMap<>();
        map.put("vishal", CAloops.list(new Integer(10)));
        return (map);
    }

    @Override
    public HashMap<String, Locus> printedLayerLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("vishal", Locus.locusV());
        return (map);
    }

    @Override
    public HashMap<String, Integer> printedLayerBitSize() {
        HashMap<String, Integer> map = new HashMap<>();
        map.put("vishal", 3);
        return (map);
    }
}
