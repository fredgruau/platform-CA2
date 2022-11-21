
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
    public List<String> directInit() {
        return CAloops.list("llseed", "tmp1", "tmp2");
    }

    public int CAmemWidth() {
        return 3;
    }

    @Override
    public HashMap<String, List<Integer>> fieldOffset() {
        HashMap<String, List<Integer>> map = new HashMap<>();
        map.put("llseed", CAloops.list(new Integer(0)));
        map.put("tmp1", CAloops.list(new Integer(1)));
        map.put("tmp2", CAloops.list(new Integer(2)));
        return (map);
    }

    @Override
    public HashMap<String, Locus> fieldLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("llseed", Locus.locusV());
        map.put("tmp1", Locus.locusV());
        map.put("tmp2", Locus.locusV());
        return (map);
    }

    @Override
    public HashMap<String, Integer> fieldBitSize() {
        HashMap<String, Integer> map = new HashMap<>();
        return (map);
    }
}


