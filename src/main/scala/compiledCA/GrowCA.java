
package compiledCA;
import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops;
import simulator.PrShift;

import java.util.HashMap;

import static compiledLoops.BasicMoves.*;

/**
 * This illustrate an example of the files that should be produced by the compiler in order to describe a CA
 */


public final class GrowCA implements CAloops {

    @Override
    public void theLoops(int[][] mem, PrShift p) {
        grow(p, mem[0], mem[3], mem[4], mem[5], mem[6], mem[7], mem[8]);
    }


    @Override
    public List<String> directInit() {
        return CAloops.list("llseed", "tmp1", "tmp2", "defE", "defF", "defVe");//
        // ,"defVe"
    }

    public int CAmemWidth() {
        return 14;
    }

    @Override
    public HashMap<String, List<Integer>> fieldOffset() {
        HashMap<String, List<Integer>> map = new HashMap<>();
        map.put("llseed", CAloops.list(new Integer(0)));
        map.put("tmp1", CAloops.list(new Integer(1)));
        map.put("tmp2", CAloops.list(new Integer(2)));
        map.put("defVe", CAloops.list(new Integer(3), new Integer(4), new Integer(5), new Integer(6), new Integer(7), new Integer(8)));
        map.put("defE", CAloops.list(new Integer(9), new Integer(10), new Integer(11)));
        map.put("defF", CAloops.list(new Integer(12), new Integer(13)));
        return (map);
    }

    @Override
    public HashMap<String, Locus> fieldLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("llseed", Locus.locusV());
        map.put("tmp1", Locus.locusV());
        map.put("tmp2", Locus.locusV());
        map.put("defVe", Locus.locusVe());
        map.put("defE", Locus.locusE());
        map.put("defF", Locus.locusF());
        return (map);
    }

    @Override
    public HashMap<String, Integer> fieldBitSize() {
        HashMap<String, Integer> map = new HashMap<>();
        return (map);
    }
}


