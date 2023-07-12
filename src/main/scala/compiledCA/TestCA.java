package compiledCA;

import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops;
import simulator.CAloops2;
import simulator.PrShift;

import java.util.HashMap;


/**
 * This illustrate an example of the files that should be produced by the compiler in order to describe a CA
 */
public final class TestCA implements CAloops2 {


    @Override
    public void theLoops(PrShift p) {

    }

    @Override
    public List<String> directInit() {
        return CAloops.list("seed");
    }

    public int CAmemWidth() {
        return 1;
    }

    @Override
    public void anchorFieldInMem(int[][] m) {

    }


    @Override
    public HashMap<String, List<Integer>> fieldOffset() {
        HashMap<String, List<Integer>> map = new HashMap<>();
        map.put("vishal", CAloops.list(new Integer(10)));
        return (map);
    }

    @Override
    public HashMap<String, Locus> fieldLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("vishal", Locus.locusV());
        return (map);
    }

    @Override
    public HashMap<String, Integer> fieldBitSize() {
        HashMap<String, Integer> map = new HashMap<>();
        map.put("vishal", 3);
        return (map);
    }
}
